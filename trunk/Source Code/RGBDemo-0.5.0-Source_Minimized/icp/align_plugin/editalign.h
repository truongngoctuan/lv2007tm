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

#ifndef EditAlignPLUGIN_H
#define EditAlignPLUGIN_H

#include "align/AlignPair.h" 
#include "align/OccupancyGrid.h" 
#include "meshtree.h"
#include <string>

class EditAlignPlugin
{	
	enum 
	{
		ALIGN_IDLE = 0x01,
		ALIGN_INSPECT_ARC = 0x02,
		ALIGN_MOVE = 0x03
	};

public:
    EditAlignPlugin();
	virtual ~EditAlignPlugin() {
		mode=ALIGN_IDLE;
	}

  	int mode;
	//nhminh
	MeshNode *currentNode() 
	{
		return meshTree.getCurrentNode();
	} 

	// nhminh
	// be careful with EditAlign.cpp : recalcCurrentArc, alignParamCurrent, 
	// current align result : fixedId, moveId, matrix
    vcg::AlignPair::Result *currentArc() 
	{
		return NULL;
	}
	MeshTree meshTree;

public:
	vcg::AlignPair::Param defaultAP;  // default alignment parameters
	

public:
	bool process();
	void recalcCurrentArc();
	bool glueByPicking(std::string strPairs);
	void printMat(std::string strResultDir);
};

#endif
