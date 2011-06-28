#include <stdio.h>
#include <string>
#include <stdio.h>  /* defines FILENAME_MAX */
#include <Windows.h>
#include "MyAlign.h"
#include <time.h>
#include <fstream>
using namespace std;

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

int main()
{
	string strDirectory = ExePath();
	string strScript = strDirectory + '\\' + "script.txt";
	int nPointClouds, nPairs;
	string *pPointClouds, *pFix, *pMov, *pPairs;
	pPointClouds = pFix = pMov = pPairs = NULL;

	if(!ReadScript(strScript, nPointClouds, nPairs, &pPointClouds, &pFix, &pMov, &pPairs))
	{
		printf("Error reading script.txt\n");
		return 0;
	}
	
	MyAlign myAlign;
	for(int i = 0; i < nPointClouds; i++)
	{
		clock_t addNodeStart = clock();
		string strModel = strDirectory + '\\' + pPointClouds[i];
		myAlign.AddNode(strModel, getName(pPointClouds[i]));
		printf("\tAdd Nodes Time elapsed: %f\n", ((double)clock() - addNodeStart) / CLOCKS_PER_SEC);
	}

	// start node
	myAlign.SetBaseNode(getName(pPointClouds[0]));

	// for each new node, align with a fixed node
	// strName1 : name of an aligned node or base node
	// strName2 : name of a new node
	// strPair : 
	// useICP : 
	
	for(int i = 0; i < nPairs; i++)
	{
		clock_t estimateStart = clock();
		myAlign.Align(getName(pFix[i]), getName(pMov[i]), strDirectory + '\\' + pPairs[i]);
		printf("\Estimate Time elapsed: %f\n", ((double)clock() - estimateStart) / CLOCKS_PER_SEC);
	}
	// Finalize with ICP
	clock_t icpStart = clock();
	myAlign.FinalizeICP();
	printf("\tICP Time elapsed: %f\n", ((double)clock() - icpStart) / CLOCKS_PER_SEC);

	// print all matrix
	myAlign.PrintResult();
	//myAlign.Export();

	if(pPointClouds)
		delete[] pPointClouds;
	if(pFix)
		delete[] pFix;
	if(pMov)
		delete[] pMov;
	if(pPairs)
		delete[] pPairs;
	return 0;
}

/*
int main()
{
	string strDirectory = ExePath();
	
	string strModel1 = strDirectory + '\\' + "mesh1.ply";
	string strModel2 = strDirectory + '\\' + "mesh2.ply";
	string strPair = strDirectory + '\\' + "pairs.txt";
	
	string strName1 = getName(strModel1);
	string strName2 = getName(strModel2);

	MyAlign myAlign;
	
	clock_t addNodeStart = clock();

	myAlign.AddNode(strModel1, strName1);
	myAlign.AddNode(strModel2, strName2);

	printf("\tAdd Nodes Time elapsed: %f\n", ((double)clock() - addNodeStart) / CLOCKS_PER_SEC);
	// start node
	myAlign.SetBaseNode(strName1);

	// for each new node, align with a fixed node
	// strName1 : name of an aligned node or base node
	// strName2 : name of a new node
	// strPair : 
	// useICP : 

	clock_t estimateStart = clock();

	myAlign.Align(strName1, strName2, strPair);

	printf("\Estimate Time elapsed: %f\n", ((double)clock() - estimateStart) / CLOCKS_PER_SEC);
	
	// Finalize with ICP
	clock_t icpStart = clock();

	myAlign.FinalizeICP();

	printf("\tICP Time elapsed: %f\n", ((double)clock() - icpStart) / CLOCKS_PER_SEC);
	// print all matrix
	myAlign.PrintResult();
	//myAlign.Export();
	return 0;
}
*/