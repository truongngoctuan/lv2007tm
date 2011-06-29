#include "util.h"

string getName(string strFile)
{
	string name;
	int lastSlash = strFile.find_last_of('\\');
	int lastDot = strFile.find_last_of('.');

	if(lastSlash == -1)
	{
		name = strFile.substr(0, lastDot);
	}
	else
	{
		name = strFile.substr(lastSlash + 1, lastDot - lastSlash - 1);
	}
	return name;
}

string getExtension(string strFile)
{
	string ext;
	int lastDot = strFile.find_last_of('.');

	if(lastDot == -1)
	{
		ext = "";
	}
	else
	{
		ext = strFile.substr(lastDot + 1, strFile.length() - lastDot - 1);
	}
	return ext;
}
