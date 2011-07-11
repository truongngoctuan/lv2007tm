#include "MyAlign.h"
#include <Windows.h>
#include <time.h>
#include <fstream>
using namespace std;

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
	return editAlignPlugin.process();
}

bool MyAlign::FinalizeICP2()
{
	for(int i = 0; i < editAlignPlugin.meshTree.nodeList.size(); i++)
	{
		MeshNode *p = editAlignPlugin.meshTree.nodeList.at(i);
		p->glued = true;
	}
	return editAlignPlugin.process();
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

void MyAlign::PrintResult(std::string strResultDir)
{
	editAlignPlugin.printMat(strResultDir);
}

void MyAlign::Export()
{
	for(int i = 0; i < editAlignPlugin.meshTree.nodeList.size(); i++)
	{
		MeshNode *p = editAlignPlugin.meshTree.nodeList.at(i);
		baseIOPlugin.save("PLY", "d:\\" + p->m->strName + "out.ply", *(p->m), 0);
	}
}
string ExePath() {
    char buffer[MAX_PATH];
    GetModuleFileNameA( NULL, buffer, MAX_PATH );
    string::size_type pos = string( buffer ).find_last_of( "\\/" );
    return string( buffer ).substr( 0, pos);
}


string getName(string strFile)
{
	string strName;
	int lastBackSlash = strFile.find_last_of('\\');
	int lastDot = strFile.find_last_of('.');
	if(lastBackSlash == -1)
	{
		strName = strFile.substr(0, lastDot);
	}
	else
	{
		strName = strFile.substr(lastBackSlash + 1, lastDot - lastBackSlash - 1);
	}
	return strName;
}

bool ReadScript(string strScript, int &nPointClouds, int &nPairs, string **pPointClouds, string **pFix, string **pMov, string **pPairs)
{
	try
	{
		ifstream in(strScript.c_str());

		nPointClouds = 0;
		in >> nPointClouds;
		*pPointClouds = new string [nPointClouds];
		string strPointCloud;
		for(int i = 0; i < nPointClouds; i++)
		{
			in >> (*pPointClouds)[i];
		}

		nPairs = 0;
		in >> nPairs;
		*pFix = new string [nPairs];
		*pMov = new string [nPairs];
		*pPairs = new string [nPairs];
		for(int i = 0; i < nPairs; i++)
		{
			in >> (*pFix)[i];
			in >> (*pMov)[i];
			in >> (*pPairs)[i];
		}
		in.close();
	}
	catch(...)
	{
		return false;
	}
	return true;
}

bool ReadScript2(string strScript, int &nPointClouds, string **pPointClouds)
{
	try
	{
		ifstream in(strScript.c_str());

		nPointClouds = 0;
		in >> nPointClouds;
		*pPointClouds = new string [nPointClouds];
		string strPointCloud;
		for(int i = 0; i < nPointClouds; i++)
		{
			in >> (*pPointClouds)[i];
		}
		in.close();
	}
	catch(...)
	{
		return false;
	}
	return true;
}


bool MyAlign::Auto2(std::string strScriptFile, std::string strResultDir)
{
	string strDirectory = ExePath();
	//string strScript = strDirectory + '\\' + strScriptFile;
	string strScript = strScriptFile;

	int nPointClouds, nPairs;
	string *pPointClouds = NULL;

	if(!ReadScript2(strScript, nPointClouds, &pPointClouds))
	{
		printf("Error reading script.txt\n");
		return false;
	}
	
	MyAlign myAlign;
	for(int i = 0; i < nPointClouds; i++)
	{
		clock_t addNodeStart = clock();
		//string strModel = strDirectory + '\\' + pPointClouds[i];
		string strModel = pPointClouds[i];
		myAlign.AddNode(strModel, getName(pPointClouds[i]));
		printf("\tAdd Nodes Time elapsed: %f\n", ((double)clock() - addNodeStart) / CLOCKS_PER_SEC);
	}

	// start node
	myAlign.SetBaseNode(getName(pPointClouds[0]));

	// Finalize with ICP
	clock_t icpStart = clock();
	bool bFinalized = myAlign.FinalizeICP2();
	printf("\tICP Time elapsed: %f\n", ((double)clock() - icpStart) / CLOCKS_PER_SEC);

	// print all matrix
	myAlign.PrintResult(strResultDir);
	//myAlign.Export();

	if(pPointClouds)
		delete[] pPointClouds;
	return bFinalized;
}	

bool MyAlign::Auto(std::string strScriptFile, std::string strResultDir)
{
	string strDirectory = ExePath();
	//string strScript = strDirectory + '\\' + strScriptFile;
	string strScript = strScriptFile;

	int nPointClouds, nPairs;
	string *pPointClouds = NULL;
	string *pFix = NULL;
	string *pMov = NULL;
	string *pPairs = NULL;

	if(!ReadScript(strScript, nPointClouds, nPairs, &pPointClouds, &pFix, &pMov, &pPairs))
	{
		printf("Error reading script.txt\n");
		return false;
	}
	
	MyAlign myAlign;
	for(int i = 0; i < nPointClouds; i++)
	{
		clock_t addNodeStart = clock();
		//string strModel = strDirectory + '\\' + pPointClouds[i];
		string strModel = pPointClouds[i];
		myAlign.AddNode(strModel, getName(pPointClouds[i]));
		printf("\tAdd Nodes Time elapsed: %f\n", ((double)clock() - addNodeStart) / CLOCKS_PER_SEC);
	}

	// start node
	myAlign.SetBaseNode(getName(pPointClouds[0]));


	clock_t align = clock();
	for(int i = 0; i < nPairs; i++)
	{
		if (!myAlign.Align(getName(pFix[i]), getName(pMov[i]), pPairs[i]))
		{
			printf("fail at: %d\n", i);
		}
	}
	printf("\talign Time elapsed: %f\n", ((double)clock() - align) / CLOCKS_PER_SEC);

	// Finalize with ICP
	clock_t icpStart = clock();
	//bool bFinalized = myAlign.FinalizeICP();
	bool bFinalized = true;
	printf("\tICP Time elapsed: %f\n", ((double)clock() - icpStart) / CLOCKS_PER_SEC);

	// print all matrix
	myAlign.PrintResult(strResultDir);
	//myAlign.Export();

	if(pPointClouds)
		delete[] pPointClouds;
	return bFinalized;
}	


bool MyAlign::AlignNotICP(std::string strScriptFile, std::string strResultDir)
{
	string strDirectory = ExePath();
	//string strScript = strDirectory + '\\' + strScriptFile;
	string strScript = strScriptFile;

	int nPointClouds, nPairs;
	string *pPointClouds = NULL;
	string *pFix = NULL;
	string *pMov = NULL;
	string *pPairs = NULL;

	if(!ReadScript(strScript, nPointClouds, nPairs, &pPointClouds, &pFix, &pMov, &pPairs))
	{
		printf("Error reading script.txt\n");
		return false;
	}
	
	MyAlign myAlign;
	for(int i = 0; i < nPointClouds; i++)
	{
		clock_t addNodeStart = clock();
		//string strModel = strDirectory + '\\' + pPointClouds[i];
		string strModel = pPointClouds[i];
		myAlign.AddNode(strModel, getName(pPointClouds[i]));
		printf("\tAdd Nodes Time elapsed: %f\n", ((double)clock() - addNodeStart) / CLOCKS_PER_SEC);
	}

	// start node
	myAlign.SetBaseNode(getName(pPointClouds[0]));

	clock_t align = clock();
	bool bResult = true;
	for(int i = 0; i < nPairs; i++)
	{
		if (!myAlign.Align(getName(pFix[i]), getName(pMov[i]), pPairs[i]))
		{
			bResult = false;
			printf("fail at: %d\n", i);
		}
	}
	printf("\talign Time elapsed: %f\n", ((double)clock() - align) / CLOCKS_PER_SEC);

	// print all matrix
	myAlign.PrintResult(strResultDir);
	//myAlign.Export();

	if(pPointClouds)
		delete[] pPointClouds;
	return bResult;
}	
