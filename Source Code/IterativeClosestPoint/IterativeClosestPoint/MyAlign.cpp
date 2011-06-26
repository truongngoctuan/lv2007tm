#include "MyAlign.h"

MyAlign::MyAlign(void)
{
	editAlignPlugin.meshTree.clear();
}

MyAlign::~MyAlign(void)
{
}

bool MyAlign::AddNode(std::string strFile, std::string strName)
{
	MeshModel *pModel = new MeshModel();
	int mask = 0;
	bool open = false;
	if(baseIOPlugin.open("PLY", strFile, *pModel, mask))
	{
		vcg::tri::UpdateBounding<CMeshO>::Box(pModel->cm);	
		pModel->strName = strName;
		pModel->strFile = strFile;
		open = true;
	}
	else
	{
		printf("can't open %s \n", strFile.c_str());
		delete pModel;
		pModel = NULL;
		return false;
	}
	
	int id = nNode;
	MeshNode* pMeshNode = new MeshNode(pModel, id);	
	editAlignPlugin.meshTree.nodeList.push_back(pMeshNode);
	nNode++;
	return true;
}

bool MyAlign::Align(string strFixName, string strMovName, string strPair)
{
	MeshNode *pFixNode = editAlignPlugin.meshTree.find(strFixName);
	MeshNode *pMovNode = editAlignPlugin.meshTree.find(strMovName);
	
	if(pFixNode->glued != true)
		return false;

	pFixNode->glued = true;
	pMovNode->glued = false;

	editAlignPlugin.meshTree.pBaseNode = pFixNode;
	editAlignPlugin.meshTree.pCurrentNode = pMovNode;

	
	if(!editAlignPlugin.glueByPicking(strPair))
	{
		return false;		
	}

	pMovNode->glued = true;
	return true;
}

bool MyAlign::FinalizeICP()
{
	editAlignPlugin.process();
	return true;
}

bool MyAlign::SetBaseNode(std::string strName)
{
	MeshNode *pFixNode = editAlignPlugin.meshTree.find(strName);
	if(pFixNode)
	{
		pFixNode->glued = true;
		return true;
	}
	return false;
}

void MyAlign::PrintResult()
{
	editAlignPlugin.printMat();
}