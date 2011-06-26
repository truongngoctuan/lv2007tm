#include <stdio.h>
#include <string>
#include <stdio.h>  /* defines FILENAME_MAX */
#include <Windows.h>
#include "MyAlign.h"
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

int main()
{
	string strDirectory = ExePath();
	
	string strModel1 = strDirectory + '\\' + "mesh1.ply";
	string strModel2 = strDirectory + '\\' + "mesh2.ply";
	string strPair = strDirectory + '\\' + "pairs.txt";
	
	string strName1 = getName(strModel1);
	string strName2 = getName(strModel2);

	MyAlign myAlign;
	myAlign.AddNode(strModel1, strName1);
	myAlign.AddNode(strModel2, strName2);

	// start node
	myAlign.SetBaseNode(strName1);

	// for each new node, align with a fixed node
	// strName1 : name of an aligned node or base node
	// strName2 : name of a new node
	// strPair : 
	// useICP : 
	myAlign.Align(strName1, strName2, strPair);


	// Finalize with ICP
	//myAlign.FinalizeICP();
	// print all matrix
	myAlign.PrintResult();
	return 0;
}