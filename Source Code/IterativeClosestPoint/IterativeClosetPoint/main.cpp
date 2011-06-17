#include <stdio.h>
#include <string>
#include "common/MeshModel.h"
#include "io_base/baseio.h"
#include "align_plugin/editalign.h"


using namespace std;
int main()
{
	MeshModel *pModel1 = NULL;
	MeshModel *pModel2 = NULL;

	string strModel1 = "e:\\My Documents\\Visual Studio 2010\\Projects\\IterativeClosestPoint\\IterativeClosetPoint\\mesh1.ply";
	string strModel2 = "e:\\My Documents\\Visual Studio 2010\\Projects\\IterativeClosestPoint\\IterativeClosetPoint\\mesh2.ply";

	pModel1 = new MeshModel();	
	pModel2 = new MeshModel();

	BaseMeshIOPlugin baseIOPlugin;
	int mask1 = 0;
	int mask2 = 0;
	bool open1 = false;
	bool open2 = false;

	if(baseIOPlugin.open("PLY", strModel1, *pModel1, mask1))
	{
		vcg::tri::UpdateBounding<CMeshO>::Box(pModel1->cm);	
		open1 = true;
	}
	if(baseIOPlugin.open("PLY", strModel2, *pModel2, mask2))
	{
		vcg::tri::UpdateBounding<CMeshO>::Box(pModel2->cm);	
		open2 = true;
	}

	MeshNode* pMeshNode1 = new MeshNode(pModel1, 0);
	MeshNode* pMeshNode2 = new MeshNode(pModel2, 1);
	EditAlignPlugin editAlignPlugin;
	editAlignPlugin.meshTree.clear();
	editAlignPlugin.meshTree.nodeList.push_back(pMeshNode1);
	editAlignPlugin.meshTree.nodeList.push_back(pMeshNode2);

	pMeshNode1->glued = true;
	pMeshNode2->glued = false;

	editAlignPlugin.meshTree.pBaseNode = pMeshNode1;
	editAlignPlugin.meshTree.pCurrentNode = pMeshNode2;

	if(editAlignPlugin.glueByPicking())
	{
		pMeshNode2->glued = true;
		editAlignPlugin.process();
	}
	return 0;
}