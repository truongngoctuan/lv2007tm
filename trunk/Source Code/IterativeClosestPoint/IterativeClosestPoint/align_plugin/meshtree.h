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

#ifndef EDITALIGN_MESHTREE_H
#define EDITALIGN_MESHTREE_H

#include "align/AlignPair.h" 
#include "align/OccupancyGrid.h" 
#include <vector>
#include <string>
#include "../common/MeshModel.h"

//WARNING!!!!!!!! : the id should be removed using instead the MeshModel's id


class MeshNode
{
public:
	MeshNode(MeshModel *_m, int _id)
	{
		m = _m;
		id = _id;
		glued = false;
	}
	MeshNode() { m=0;id=-1;}
	bool glued;
	int id;
	MeshModel *m;
	vcg::Matrix44f &tr() 
	{
		return m->cm.Tr;
	}
	const vcg::Box3f &bbox() const 
	{
		return m->cm.bbox;
	}
};

class MeshTree
{
	public:
	MeshTree();
	
	std::vector<MeshNode *> nodeList;
	vcg::OccupancyGrid OG;
	std::vector<vcg::AlignPair::Result> ResVec;
	std::vector<vcg::AlignPair::Result *> ResVecPtr;
	MeshNode *pBaseNode;
	MeshNode *pCurrentNode;
	
	MeshModel *MM(unsigned int i) {return nodeList.at(i)->m;}
	
	void clear()
	{
		for(int i = 0; i < nodeList.size(); i++)
		{
			delete nodeList.at(i);
		}

		nodeList.clear();
		ResVec.clear();
		ResVecPtr.clear();
	}

	void resetID();

	MeshNode *find(int id)
	{
		for(int i = 0; i < nodeList.size(); i++)
		{
			MeshNode *mp =  nodeList.at(i);
			if(mp->id==id) 
				return mp;
		}		
		assert("You are trying to find an unexistent mesh"==0);
		return 0;
	}

	MeshNode *find(MeshModel *m)
	{
		for(int i = 0; i < nodeList.size(); i++)
		{
			MeshNode *mp =  nodeList.at(i);
			if(mp->m==m) 
				return mp;
		}			
		assert("You are trying to find an unexistent mesh"==0);
		return 0;
	}

	MeshNode *find(std::string strName)
	{
		for(int i = 0; i < nodeList.size(); i++)
		{
			MeshNode *mp =  nodeList.at(i);
			if(mp->m->strName.compare(strName) == 0) 
				return mp;
		}			
		assert("You are trying to find an unexistent mesh"==0);
		return 0;
	}
	int gluedNum();

	
	void Process(vcg::AlignPair::Param &ap);
	void ProcessGlobal(vcg::AlignPair::Param &ap);
	void ProcessArc(int fixId, int movId, vcg::AlignPair::Result &result, vcg::AlignPair::Param ap);
	void ProcessArc(int fixId, int movId, vcg::Matrix44d &MovToFix, vcg::AlignPair::Result &result, vcg::AlignPair::Param ap);

	inline vcg::Box3f bbox() 
	{
		vcg::Box3f FullBBox;
		for(int i = 0; i < nodeList.size(); i++)
		{
			MeshNode *mp =  nodeList.at(i);
			FullBBox.Add(vcg::Matrix44f::Construct(mp->tr()),mp->bbox());
		}	
		return FullBBox;
	}

	inline vcg::Box3f gluedBBox() 
	{
		vcg::Box3f FullBBox;

		for(int i = 0; i < nodeList.size(); i++)
		{
			MeshNode *mp =  nodeList.at(i);
			if(mp->glued)
					FullBBox.Add(vcg::Matrix44f::Construct(mp->tr()),mp->bbox());
		}
		return FullBBox;
	}	

	MeshNode *getBaseNode()
	{
		return pBaseNode;
	}
	MeshNode *getCurrentNode()
	{
		return pCurrentNode;
	}
};
#endif
