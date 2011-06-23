/****************************************************************************
 * MeshLab                                                           o o     *
 * A versatile mesh processing toolbox                             o     o   *
 *                                                                _   O  _   *
 * Copyright(C) 2005                                                \/)\/    *
 * Visual Computing Lab                                            /\/|      *
 * ISTI - Italian National Research Council                           |      *
 *                                                                    \      *
 * All rights reserved.                                                      *
 *                                                                           *
 * This program is free software; you can redistribute it and/or modify      *   
 * it under the terms of the GNU General Public License as published by      *
 * the Free Software Foundation; either version 2 of the License, or         *
 * (at your option) any later version.                                       *
 *                                                                           *
 * This program is distributed in the hope that it will be useful,           *
 * but WITHOUT ANY WARRANTY; without even the implied warranty of            *
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the             *
 * GNU General Public License (http://www.gnu.org/licenses/gpl.txt)          *
 * for more details.                                                         *
 *                                                                           *
 ****************************************************************************/

#include "meshtree.h"
#include "align/AlignGlobal.h"

MeshTree::MeshTree()
{
}

int MeshTree::gluedNum()
{
	int cnt=0;
	for(int i = 0; i < nodeList.size(); i++)
	{
		MeshNode *mn =  nodeList.at(i);
		if(mn->glued) 
			++cnt;
	}	
	return cnt;
}

// Assign to each mesh (glued and not glued) an unique id
void MeshTree::resetID()
{
	int cnt=0;
	for(int i = 0; i < nodeList.size(); i++)
	{
		MeshNode *mn =  nodeList.at(i);
		mn->id= cnt;
		cnt++;
	}	
}

void MeshTree::ProcessArc(int fixId, int movId, vcg::AlignPair::Result &result, vcg::AlignPair::Param ap)
{
    // l'allineatore globale cambia le varie matrici di posizione di base delle mesh
    // per questo motivo si aspetta i punti nel sistema di riferimento locale della mesh fix
    // Si fanno tutti i conti rispetto al sistema di riferimento locale della mesh fix
	vcg::Matrix44d FixM=vcg::Matrix44d::Construct(find(fixId)->tr());		
	vcg::Matrix44d MovM=vcg::Matrix44d::Construct(find(movId)->tr());		
	vcg::Matrix44d MovToFix = Inverse(FixM) * MovM;
    
	ProcessArc(fixId,movId,MovToFix,result,ap);
}
/** This is the main alignment function.
  It takes a pair of mesh and aling the second on the first one according to the parameters stored in <ap>

  */
void MeshTree::ProcessArc(int fixId, int movId, vcg::Matrix44d &MovM, vcg::AlignPair::Result &result, vcg::AlignPair::Param ap)
{
	vcg::AlignPair::A2Mesh Fix, Mov;
	vcg::AlignPair aa;

	// 1) Convert fixed mesh and put it into the grid.
	aa.ConvertMesh<CMeshO>(MM(fixId)->cm,Fix);

	vcg::AlignPair::A2Grid UG;
	vcg::AlignPair::A2GridVert VG;

	if(MM(fixId)->cm.fn==0 || ap.UseVertexOnly)
	{
		Fix.InitVert(vcg::Matrix44d::Identity(),false);
		vcg::AlignPair::InitFixVert(&Fix,ap,VG);
	}
	else
	{
		Fix.Init(vcg::Matrix44d::Identity(),false);
		vcg::AlignPair::InitFix(&Fix, ap, UG);
	}
	// 2) Convert the second mesh and sample a <ap.SampleNum> points on it.

	aa.ConvertMesh<CMeshO>(MM(movId)->cm,Mov);
	std::vector<vcg::AlignPair::A2Vertex> tmpmv;     
	aa.ConvertVertex(Mov.vert,tmpmv);
	aa.SampleMovVert(tmpmv, ap.SampleNum, ap.SampleMode);

	aa.mov=&tmpmv;
	aa.fix=&Fix;
	aa.ap = ap;

	vcg::Matrix44d In=MovM;
	// Perform the ICP algorithm
	aa.Align(In,UG,VG,result);

	result.FixName=fixId;
	result.MovName=movId;
	result.as.Dump(stdout);
}

void MeshTree::Process(vcg::AlignPair::Param &ap)
{
	//QString buf;
	//cb(0,qPrintable(buf.sprintf("Starting Processing of %i glued meshes out of %i meshes\n",gluedNum(),nodeList.size())));

	resetID(); 	// Assign to each mesh (glued and not glued) an unique id
	
	/******* Occupancy Grid Computation *************/
	//cb(0,qPrintable(buf.sprintf("Computing Overlaps %i glued meshes...\n",gluedNum() )));
	OG.Init(nodeList.size(), vcg::Box3d::Construct(gluedBBox()), 10000);
	for(int i = 0; i < nodeList.size(); i++)
	{
		MeshNode *mn =  nodeList.at(i);
		if(mn->glued)
			OG.AddMesh<CMeshO>(mn->m->cm, vcg::Matrix44d::Construct(mn->tr()), mn->id);
	}			
	
	OG.Compute();
	OG.Dump(stdout);
	// Note: the s and t of the OG translate into fix and mov, respectively.		
  
	
	/*************** The long loop of arc computing **************/
	
	ResVec.clear();
	ResVec.resize(OG.SVA.size());
	ResVecPtr.clear();

	//cb(0,qPrintable(buf.sprintf("Computed %i possible Arcs :\n",int(OG.SVA.size()))));
	size_t i=0;
	for(i=0;i<OG.SVA.size() && OG.SVA[i].norm_area > .1; ++i)
	{	
		fprintf(stdout,"%4i -> %4i Area:%5i NormArea:%5.3f\n",OG.SVA[i].s,OG.SVA[i].t,OG.SVA[i].area,OG.SVA[i].norm_area);
		ProcessArc(OG.SVA[i].s, OG.SVA[i].t, ResVec[i], ap);

		ResVec[i].area= OG.SVA[i].norm_area;
		
		if( ResVec[i].IsValid() )
			ResVecPtr.push_back(&ResVec[i]);
		std::pair<double,double> dd=ResVec[i].ComputeAvgErr();
		if( ResVec[i].IsValid() )  
		{
			printf("===========================================================\n");
			printf("(%2i/%i) %2i -> %2i Aligned AvgErr dd=%f -> dd=%f \n",int(i+1),int(OG.SVA.size()),OG.SVA[i].s,OG.SVA[i].t,dd.first,dd.second);
			printf("===========================================================\n");
			
			//cb(0,qPrintable(buf.sprintf("(%2i/%i) %2i -> %2i Aligned AvgErr dd=%f -> dd=%f \n",int(i+1),int(OG.SVA.size()),OG.SVA[i].s,OG.SVA[i].t,dd.first,dd.second)));
		}
		else
		{
			printf("===========================================================\n");
			printf("(%2i/%i) %2i -> %2i Failed Alignment of one arc \n"  ,int(i+1),int(OG.SVA.size()),OG.SVA[i].s,OG.SVA[i].t);
			printf("===========================================================\n");
			//cb(0,qPrintable(buf.sprintf("(%2i/%i) %2i -> %2i Failed Alignment of one arc \n"  ,int(i+1),int(OG.SVA.size()),OG.SVA[i].s,OG.SVA[i].t)));
		}
			
		
	}
	// now cut the ResVec vector to the only computed result (the arcs with area > .1)
	ResVec.resize(i);
  
	//cb(0,qPrintable(buf.sprintf("Completed Mesh-Mesh Alignment\n")));
	
	//if there are no arcs at all complain and return
	if(ResVec.size()==0) 
	{
		printf("===========================================================\n");
		printf("\n Failure. There are no overlapping meshes?\n No candidate alignment arcs. Nothing Done.\n");
		printf("===========================================================\n");
		//cb(0,qPrintable(buf.sprintf("\n Failure. There are no overlapping meshes?\n No candidate alignment arcs. Nothing Done.\n")));
		return;
	}
	
	
	//if there are no valid arcs complain and return
	if(ResVecPtr.size()==0) 
	{
		printf("===========================================================\n");
		printf("\n Failure. No succesful arc among candidate Alignment arcs. Nothing Done.\n");
		printf("===========================================================\n");
		//cb(0,qPrintable(buf.sprintf("\n Failure. No succesful arc among candidate Alignment arcs. Nothing Done.\n")));
		return;
	}
	
	ProcessGlobal(ap);	
	printf("===========================================================\n");
	printf("Completed\n");
	printf("===========================================================\n");
}

void MeshTree::ProcessGlobal(vcg::AlignPair::Param &ap)
{
	/************** Preparing Matrices for global alignment *************/
	//cb(0,qPrintable(buf.sprintf("Starting Global Alignment\n")));

	vcg::Matrix44d Zero44; Zero44.SetZero();
	std::vector<vcg::Matrix44d> PaddedTrVec(nodeList.size(),Zero44);
	// matrix trv[i] is relative to mesh with id IdVec[i]
	// if all the mesh are glued GluedIdVec=={1,2,3,4...}
	std::vector<int> GluedIdVec;
	std::vector<vcg::Matrix44d> GluedTrVec;
		
	std::vector<std::string> names(nodeList.size());
	
	for(int i = 0; i < nodeList.size(); i++)
	{
		MeshNode *mn =  nodeList.at(i);
		if(mn->glued)
		{
			GluedIdVec.push_back(mn->id);							
			GluedTrVec.push_back(vcg::Matrix44d::Construct(mn->tr()));				
			PaddedTrVec[mn->id]=GluedTrVec.back();
		}
	}	
		
	vcg::AlignGlobal AG;
	AG.BuildGraph(ResVecPtr, GluedTrVec, GluedIdVec);
   
	int maxiter = 1000;
	float StartGlobErr = 0.001f;
	while(!AG.GlobalAlign(names, StartGlobErr, 100, true, stdout))
	{
		StartGlobErr*=2;
		AG.BuildGraph(ResVecPtr,GluedTrVec, GluedIdVec);
	}

	std::vector<vcg::Matrix44d> GluedTrVecOut(GluedTrVec.size());
	AG.GetMatrixVector(GluedTrVecOut,GluedIdVec);

	//Now get back the results!
	for(int ii=0;ii<GluedTrVecOut.size();++ii)
		MM(GluedIdVec[ii])->cm.Tr.Import(GluedTrVecOut[ii]);	

	//cb(0,qPrintable(buf.sprintf("Completed Global Alignment (error bound %6.4f)\n",StartGlobErr)));

}

