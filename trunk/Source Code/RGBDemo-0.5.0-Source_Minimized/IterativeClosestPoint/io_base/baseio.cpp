/****************************************************************************
* MeshLab                                                           o o     *
* An extendible mesh processor                                    o     o   *
*                                                                _   O  _   *
* Copyright(C) 2005, 2006                                          \/)\/    *
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
#include "baseio.h"

using namespace std;
using namespace vcg;

bool BaseMeshIOPlugin::open(const string &formatName, const string &fileName, MeshModel &m, int& mask)
{
	bool normalsUpdated = false;

	// initializing mask
	mask = 0;
	
	// initializing progress bar status
	//if (cb != NULL)		(*cb)(0, "Loading...");

	string errorMsgFormat = "Error encountered while loading file:\n\"%1\"\n\nError details: %2";

	//string filename = fileName.toUtf8().data();
	string filename = fileName;
  
	if (formatName == "PLY") //uppercase
	{
		tri::io::ImporterPLY<CMeshO>::LoadMask(filename.c_str(), mask); 
		// small patch to allow the loading of per wedge color into faces. 
		 
		int result = tri::io::ImporterPLY<CMeshO>::Open(m.cm, filename.c_str(), mask);
		if (result != 0) // all the importers return 0 on success
		{
			if(tri::io::ImporterPLY<CMeshO>::ErrorCritical(result) )
			{
				//errorMessage = errorMsgFormat.arg(fileName, tri::io::ImporterPLY<CMeshO>::ErrorMsg(result));
				return false;
			}
		}
	}	
	else	if( (formatName == "OBJ") || (formatName == "QOBJ") )
	{
		tri::io::ImporterOBJ<CMeshO>::Info oi;	
		//oi.cb = cb;
		if (!tri::io::ImporterOBJ<CMeshO>::LoadMask(filename.c_str(), oi))
			return false;
	//m.Enable(oi.mask);
		
		int result = tri::io::ImporterOBJ<CMeshO>::Open(m.cm, filename.c_str(), oi);
		if (result != tri::io::ImporterOBJ<CMeshO>::E_NOERROR)
		{
			if (result & tri::io::ImporterOBJ<CMeshO>::E_NON_CRITICAL_ERROR)
						{
							string err = tri::io::ImporterOBJ<CMeshO>::ErrorMsg(result);
							//errorMessage = errorMsgFormat.arg(fileName, tri::io::ImporterOBJ<CMeshO>::ErrorMsg(result));
						}
			else
			{
				//errorMessage = errorMsgFormat.arg(fileName, tri::io::ImporterOBJ<CMeshO>::ErrorMsg(result));
				return false;
			}
		}

		if(oi.mask & tri::io::Mask::IOM_WEDGNORMAL)
			normalsUpdated = true;
		//m.Enable(oi.mask);
		//if(m.hasDataMask(MeshModel::MM_POLYGONAL)) qDebug("Mesh is Polygonal!");
		//mask = oi.mask;
	}	
	else
	{
		assert(0); // Unknown File type
		return false;
	}

	// verify if texture files are present
	//string missingTextureFilesMsg = "The following texture files were not found:\n";
	//bool someTextureNotFound = false;
	//for ( unsigned textureIdx = 0; textureIdx < m.cm.textures.size(); ++textureIdx)
	//{
 //   if (!QFile::exists(m.cm.textures[textureIdx].c_str()))
	//	{
	//		missingTextureFilesMsg.append("\n");
	//		missingTextureFilesMsg.append(m.cm.textures[textureIdx].c_str());
	//		someTextureNotFound = true;
	//	}
	//}
	//if (someTextureNotFound)
	//	Log("Missing texture files: %s", qPrintable(missingTextureFilesMsg));
	
	//if (cb != NULL)	(*cb)(99, "Done");

	return true;
}

bool BaseMeshIOPlugin::save(const string &formatName,const string &fileName, MeshModel &m, const int mask)
{
	string errorMsgFormat = "Error encountered while exportering file %1:\n%2";
	string filename = fileName;
	//string filename = fileName.toUtf8().data();
	//string ex = formatName.toUtf8().data();
	bool binaryFlag = false;
	//if(formatName == "PLY")
	//	binaryFlag = par.findParameter("Binary")->val->getBool();
					
	if(formatName == "PLY")
	{
		int result = tri::io::ExporterPLY<CMeshO>::Save(m.cm,filename.c_str(), mask, binaryFlag);
		if(result!=0)
		{
			//errorMessage = errorMsgFormat.arg(fileName, tri::io::ExporterPLY<CMeshO>::ErrorMsg(result));
			return false;
		}
		return true;
	}
	
	if(formatName == "OBJ")
	{
		int result = tri::io::Exporter<CMeshO>::Save(m.cm,filename.c_str(),mask);
		if(result!=0)
		{
			//errorMessage = errorMsgFormat.arg(fileName, tri::io::Exporter<CMeshO>::ErrorMsg(result));
			return false;
		}
		return true;
	}

	assert(0); // unknown format
	return false;
}