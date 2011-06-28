#include <stdio.h>
#include <string>
#include <stdio.h>  /* defines FILENAME_MAX */
#include "MyAlign.h"
using namespace std;

int main()
{
	MyAlign::Auto("script.txt", "final.ply");
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