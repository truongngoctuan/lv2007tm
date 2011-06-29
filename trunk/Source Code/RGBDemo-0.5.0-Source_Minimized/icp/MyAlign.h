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
	bool Align(std::string strFixName, std::string strMovName, std::string strPair);
	bool FinalizeICP();
	bool FinalizeICP2();
	bool SetBaseNode(std::string strName);
	void PrintResult(std::string strResultDir);
	void Export();

	static __declspec(dllexport) bool Auto(std::string strScriptFile, std::string strResultDir);
};
