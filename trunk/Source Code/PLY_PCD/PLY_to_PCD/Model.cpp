#include "Model.h"
#include <fstream>
#include <string>
#include <stdio.h>
using namespace std;

int StringToInt(string str)
{
	bool init = false;
	int pow = 0;
	int value = 0;
	for(int i = 0; i < str.length(); i++)
	{
		if(isdigit(str[i]))
		{
			init = true;
			value = value * 10 + (str[i] - '0');
		}
		else if(init == true)
		{
			break;		
		}
	}
	return value;
}

void Model::ImportPLY(string strFile)
{
	ifstream in(strFile.c_str());
	int nPoints = 0;

	string ss;
	std::getline(in, ss);
	string strPoints = "element vertex";
	while(ss.find(strPoints) == -1)
		std::getline(in, ss);
	ss = ss.substr(strPoints.length(), ss.length() - strPoints.length());
	
	nPoints = StringToInt(ss); printf("Points : %d\n", nPoints);
	
	string strEnd = "end_header";
	while(ss.find(strEnd) == -1)
		std::getline(in, ss);

	points = new Point3D[nPoints];
	nGoodPoints = 0;
	float x, y, z;
	int r, g, b;
	for(int i = 0; i < nPoints; i++)
	{
		in >> x >> y >> z;
		in >> r >> g >> b;
		points[i] = Point3D(x, y, z, r, g, b);
		
		if(x == 0 && y == 0 && z == 0)
			continue;

		nGoodPoints++;
	}

	in.close();

	printf("GoodPoints : %d\n", nGoodPoints);
	name = getName(strFile);
}

void Model::ImportPCD(string strFile)
{
	ifstream in(strFile.c_str());
	int nPoints = 0;

	string ss;
	std::getline(in, ss);
	string strPoints = "POINTS ";
	while(ss.find(strPoints) == -1)
		std::getline(in, ss);
	ss = ss.substr(strPoints.length(), ss.length() - strPoints.length());
	
	nPoints = StringToInt(ss); printf("Points : %d\n", nPoints);
	
	string strEnd = "DATA ascii";
	while(ss.find(strEnd) == -1)
		std::getline(in, ss);

	points = new Point3D[nPoints];
	nGoodPoints = 0;
	float x, y, z;
	int color;
	int r, g, b;
	for(int i = 0; i < nPoints; i++)
	{
		in >> x >> y >> z;
		in >> color;

		r = color / (256 * 256); color -= r * 256 * 256;
		g = color / 256; color -= g * 256;
		b = color;

		points[i] = Point3D(x * 1000, y * 1000, z * 1000, r, g, b);
		
		if(x == 0 && y == 0 && z == 0)
			continue;

		nGoodPoints++;
	}

	in.close();

	printf("GoodPoints : %d\n", nGoodPoints);
	name = getName(strFile);
}

void Model::ImportPCD2(string strFile)
{
	ifstream in(strFile.c_str());
	int nPoints = 0;

	string ss;
	std::getline(in, ss);
	string strPoints = "POINTS ";
	while(ss.find(strPoints) == -1)
		std::getline(in, ss);
	ss = ss.substr(strPoints.length(), ss.length() - strPoints.length());
	
	nPoints = StringToInt(ss); printf("Points : %d\n", nPoints);
	
	string strEnd = "DATA ascii";
	while(ss.find(strEnd) == -1)
		std::getline(in, ss);

	points = new Point3D[nPoints];
	nGoodPoints = 0;
	float x, y, z;
	int color;
	int r, g, b;
	for(int i = 0; i < nPoints; i++)
	{
		in >> x >> y >> z;
		points[i] = Point3D(x * 1000, y * 1000, z * 1000, 0, 0, 0);
		
		if(x == 0 && y == 0 && z == 0)
			continue;

		nGoodPoints++;
	}

	in.close();

	printf("GoodPoints : %d\n", nGoodPoints);
	name = getName(strFile);
}


Model::Model(string strFile)
{
	if(getExtension(strFile).compare("ply") == 0)
		ImportPLY(strFile);
	else if (getExtension(strFile).compare("pcd") == 0)
		ImportPCD2(strFile);
}

Model::~Model(void)
{	
	delete[] points;
}

void Model::ExportPCD()
{
	string strFile = name + ".pcd";
	ofstream outFile(strFile.c_str());

	outFile << "# .PCD v.7 - Point Cloud Data file format" << endl;
    outFile << "VERSION .7" << endl;
    outFile << "FIELDS x y z rgb" << endl;
    outFile << "SIZE 4 4 4 4" << endl;
    outFile << "TYPE F F F F" << endl;
    outFile << "COUNT 1 1 1 1" << endl;
    outFile << "WIDTH " << nGoodPoints << endl;
    outFile << "HEIGHT " << 1 << endl;
    outFile << "POINTS " << nGoodPoints << endl;
	outFile << "DATA ascii" << endl;
	
	for(int i = 0; i < nGoodPoints; i++)
	{
		if(points[i].X == 0 && points[i].Y  == 0 && points[i].Z == 0)
			continue;		

		int color;
        //color = (vertex.Color.R << 16) | (vertex.Color.G << 8) | (vertex.Color.B << 0);
		color = (points[i].r * 256 * 256) + (points[i].g * 256) + (points[i].b);
        color = color & 0x0FFFFFFF;

		outFile << points[i].X / 1000 << " " << points[i].Y / 1000 << " " << points[i].Z / 1000 << " " << color << endl;		
	}
	outFile.close();
}

void Model::ExportPLY()
{
	string strFile = name + ".ply";
	ofstream outFile(strFile.c_str());

	outFile << "ply" << endl;
    outFile << "format ascii 1.0" << endl;
    outFile << "element vertex " << nGoodPoints << endl;
    outFile << "property float x" << endl;
    outFile << "property float y" << endl;
    outFile << "property float z" << endl;
    outFile << "property uchar red" << endl;
    outFile << "property uchar green" << endl;
    outFile << "property uchar blue" << endl;
    outFile << "end_header" << endl;

	for(int i = 0; i < nGoodPoints; i++)
	{
		if(points[i].X == 0 && points[i].Y  == 0 && points[i].Z == 0)
			continue;
		outFile << points[i].X << " " << points[i].Y << " " << points[i].Z 
			<< " " << points[i].r << " " << points[i].g << " " << points[i].b << endl;		
	}
	outFile.close();
}

void Model::ExportPLY2()
{
	string strFile = name + ".ply";
	ofstream outFile(strFile.c_str());

	outFile << "ply" << endl;
    outFile << "format ascii 1.0" << endl;
    outFile << "element vertex " << nGoodPoints << endl;
    outFile << "property float x" << endl;
    outFile << "property float y" << endl;
    outFile << "property float z" << endl;
    outFile << "end_header" << endl;

	for(int i = 0; i < nGoodPoints; i++)
	{
		if(points[i].X == 0 && points[i].Y  == 0 && points[i].Z == 0)
			continue;
		outFile << points[i].X << " " << points[i].Y << " " << points[i].Z << endl;		
	}
	outFile.close();
}