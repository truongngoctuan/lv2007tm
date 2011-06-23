#pragma once
#include <string>
#include "common/MeshModel.h"
#include "io_base/baseio.h"
#include "align_plugin/editalign.h"

class MyAlign
{
public:
	BaseMeshIOPlugin baseIOPlugin;
	EditAlignPlugin editAlignPlugin;
	int nNode;
public:
	MyAlign(void);
	~MyAlign(void);

	bool AddNode(std::string strFile, std::string strName);
	bool Align(std::string strFixName, std::string strMovName, std::string strPair, bool runICP);
	bool SetBaseNode(std::string strName);
	void PrintResult();
};
