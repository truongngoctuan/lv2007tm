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
/****************************************************************************
  History
$Log: meshedit.cpp,v $
****************************************************************************/

#include <math.h>
#include <stdlib.h>
#include <vcg/math/point_matching.h>
#include <fstream>
#include "editalign.h"
using namespace vcg;

EditAlignPlugin::EditAlignPlugin() {
}


int EPSILON = 1e-4;
bool isNearEqual(float a, float b)
{
	if(abs(a - b) > EPSILON)
		return false;
	return true;
}

bool edgeNearEqual(vcg::Point3f p1a, vcg::Point3f p1b, vcg::Point3f p2a, vcg::Point3f p2b)
{
	if(!isNearEqual(p1a.X() - p1b.X(), p2a.X() - p2b.X()))
		return false;
	if(!isNearEqual(p1a.Y() - p1b.Y(), p2a.Y() - p2b.Y()))
		return false;
	if(!isNearEqual(p1a.Z() - p1b.Z(), p2a.Z() - p2b.Z()))
		return false;
	return true;
}

bool InitFeaturePairs(std::vector<vcg::Point3f> *fixPnt, std::vector<vcg::Point3f> *movePnt, std::string strPairs)
{
	std::ifstream in(strPairs.c_str());

	int threshold = 0;
	in >> threshold;
	EPSILON = threshold;

	int num;
	in >> num;

	float x1, y1, z1;
	float x2, y2, z2;	

	// read pairs
	vcg::Point3f *pFix = new vcg::Point3f[num];
	vcg::Point3f *pMove = new vcg::Point3f[num];
	
	for(int i = 0; i < num; i++)
	{
		in >> x1; in >> y1; in >> z1;
		pFix[i].X() = x1; pFix[i].Y() = y1; pFix[i].Z() = z1;

		in >> x2; in >> y2; in >> z2;
		pMove[i].X() = x2; pMove[i].Y() = y2; pMove[i].Z() = z2;
	}
	in.close();

	// choose best pairs
	// get 4 best pairs
	int index1, index2, index3, index4;
	index1 = index2 = index3 = index4 = -1;
	bool found = false;
	for(int i1 = 0; i1 < num; i1++)
	{
		for(int i2 = 0; i2 < num; i2++)
		{
			if(i2 == i1)
				continue;

			if(!edgeNearEqual(pFix[i2], pFix[i1], pMove[i2], pMove[i1]))
				continue;
			for(int i3 = 0; i3 < num; i3++)
			{
				if(i3 == i1 || i3 == i2)
					continue;

				if(!edgeNearEqual(pFix[i3], pFix[i1], pMove[i3], pMove[i1]))
					continue;
				/*if(!edgeNearEqual(pFix[i3], pFix[i2], pMove[i3], pMove[i2]))
					continue;*/
				for(int i4 = 0; i4 < num; i4++)
				{
					if(i4 == i1 || i4 == i2 || i4 == i3)
						continue;

					if(!edgeNearEqual(pFix[i4], pFix[i1], pMove[i4], pMove[i1]))
						continue;
					/*if(!edgeNearEqual(pFix[i4], pFix[i2], pMove[i4], pMove[i2]))
						continue;
					if(!edgeNearEqual(pFix[i4], pFix[i3], pMove[i4], pMove[i3]))
						continue;*/

					found = true;
					if(found)
					{
						index1 = i1;
						index2 = i2;
						index3 = i3;
						index4 = i4;
						break;
					}
				}
				if(found)
						break;
			}
			if(found)
						break;
		}
		if(found)
						break;
	}
	if(found)	
	{
		fixPnt->push_back(pFix[index1]);
		fixPnt->push_back(pFix[index2]);
		fixPnt->push_back(pFix[index3]);
		fixPnt->push_back(pFix[index4]);

		movePnt->push_back(pMove[index1]);
		movePnt->push_back(pMove[index2]);
		movePnt->push_back(pMove[index3]);
		movePnt->push_back(pMove[index4]);
		
		for(int i = 0; i < num; i++)
		{
			if(i == index1 || i == index2 || i == index3 || i == index4)
				continue;

			if(edgeNearEqual(pFix[index1], pFix[i], pMove[index1], pMove[i]))
			{
				fixPnt->push_back(pFix[i]);
				movePnt->push_back(pMove[i]);
			}
		}
	}

	delete[] pFix;
	delete[] pMove;
	return found;
}

void PrintMatrix44(vcg::Matrix44f mat44, std::string strFile)
{
	std::ofstream out(strFile.c_str());
	for(int row = 0; row < 4; row++)
	{
		for(int col = 0; col < 4; col++)
		{
			//transpose
			//out << mat44.ElementAt(col, row);
			out << mat44.ElementAt(row, col);
			out << ' ';
		}
		out << '\n';
	}
	out.close();
}

bool EditAlignPlugin::glueByPicking(std::string strPairs)
{
	if(meshTree.gluedNum() < 1)
	{
		//QMessageBox::warning(0,"Align tool", "Point based aligning requires at least one glued  mesh");
		return false;
	}

	MeshNode *pFixNode = meshTree.getBaseNode();
	MeshNode *pMovNode = meshTree.getCurrentNode();

	// i picked points sono in due sistemi di riferimento. 
	std::vector<vcg::Point3f>freePnt;// = dd->aa->freePickedPointVec; //nhminh
	std::vector<vcg::Point3f>gluedPnt;//= dd->aa->gluedPickedPointVec; //nhminh

	InitFeaturePairs(&gluedPnt, &freePnt, strPairs);
	
	/*freePnt.push_back(vcg::Point3f(-0.0089151040, 0.078222930, -0.70964420));
	freePnt.push_back(vcg::Point3f(-0.011225247, 0.13255557, -0.72813487));
	freePnt.push_back(vcg::Point3f(0.093167111, -0.072445147, -0.80391663));
	freePnt.push_back(vcg::Point3f(-0.077288508, 0.11934438, -0.72057730));
	freePnt.push_back(vcg::Point3f(-0.024791593, 0.0099738808, -0.72088557));

	gluedPnt.push_back(vcg::Point3f(-0.067711622, 0.078488626, -0.69700104));
	gluedPnt.push_back(vcg::Point3f(-0.067837872, 0.12978132, -0.71301025));
	gluedPnt.push_back(vcg::Point3f(0.090444699, -0.075097434, -0.77900696));
	gluedPnt.push_back(vcg::Point3f(-0.13605118, 0.11539144, -0.73700190));
	gluedPnt.push_back(vcg::Point3f(-0.075538456, 0.0067144474, -0.71400803));*/

	printf("===========================================================\n");
	printf("pairs : %d\n", freePnt.size());
	printf("===========================================================\n");

	if( (freePnt.size() != gluedPnt.size())	|| (freePnt.size()==0) )	{
		//QMessageBox::warning(0,"Align tool", "require the same number of chosen points");
		return false;
	}

	if((freePnt.size() != gluedPnt.size())	|| (freePnt.size() < 4))
	{
		return false;
	}

	Matrix44f res;
	//if(dd->allowScalingCB->isChecked()) //nhminh
	if(false)
		PointMatching<float>::ComputeSimilarityMatchMatrix(res,gluedPnt,freePnt);
	else 
		PointMatching<float>::ComputeRigidMatchMatrix(res,gluedPnt,freePnt);
			
	pMovNode->tr() = pFixNode->tr() * res;
	//PrintMatrix44(res, strEstimate);
	return true;
} 
 
void EditAlignPlugin::process()
{
	if(meshTree.gluedNum() < 2)
	{
		//QMessageBox::warning(0,"Align tool", "Process can work only when more than two meshes have been glued");
		return;
	}
	meshTree.Process(defaultAP);

	/*for(int i = 0; i < meshTree.gluedNum(); i++)
	{
		if(meshTree.nodeList.at(i)->glued)
		{
			char count = '1';
			count += i;
			MeshNode *pNode = meshTree.nodeList.at(i);
			PrintMatrix44(pNode->tr(), pNode->m->strName + ".txt");
		}
	}*/	
}

// should be del, currentArc() is problem
void EditAlignPlugin::recalcCurrentArc()
{
	assert(currentArc());
	
	meshTree.ProcessArc(currentArc()->FixName,currentArc()->MovName,*currentArc(),currentArc()->ap);
	meshTree.ProcessGlobal(currentArc()->ap);
}

void EditAlignPlugin::printMat()
{
	for(int i = 0; i < meshTree.gluedNum(); i++)
	{
		if(meshTree.nodeList.at(i)->glued)
		{
			MeshNode *pNode = meshTree.nodeList.at(i);
			PrintMatrix44(pNode->tr(), pNode->m->strName + ".txt");
		}
	}
}