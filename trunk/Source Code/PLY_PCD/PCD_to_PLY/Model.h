#pragma once
#include "util.h"
#include <string>
using namespace std;

struct Point3D
{
    double X;
    double Y;
    double Z;
	int r;
	int g;
	int b;
	Point3D()
	{
		X = 0;
		Y = 0;
		Z = 0;
	}
    Point3D (double _X, double _Y, double _Z)
    {
        X = _X;
        Y = _Y;
        Z = _Z;
    }
	Point3D (double _X, double _Y, double _Z, int _r, int _g, int _b)
    {
        X = _X;
        Y = _Y;
        Z = _Z;
		r = _r;
		g = _g;
		b = _b;
    }
};

class Model
{
public:
	Point3D* points;
	string name;
	int nGoodPoints;
public:
	Model(string strFile);
	~Model(void);

	void ExportPLY();
	void ExportPLY2();
	void ExportPCD();
private:
	void ImportPLY(string strFile);
	void ImportPCD(string strFile);
	void ImportPCD2(string strFile);
};
