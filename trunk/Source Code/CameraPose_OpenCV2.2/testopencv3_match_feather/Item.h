#pragma once
#include <cv.h>
#include <string>
#include <vector>
#include "RotationMatrixUlti.h"
#include "SURFMatching.h"
#include "Util.h"
#include "GetRT.h"
using namespace std;
using namespace cv;

//using for RANSAC Threshold in IsConnectable function
#define DISTANCE_THRES 20
#define TAN_ANGLE_THRES 0.05

class Item
{
	string strFileName;
	CvSeq *imageKeypoints;
	CvSeq *imageDescriptors;
	CvMemStorage* storage;

	CvMat *transformationMat;
	static CvMat *I;
	static CvMat *GetIdentityMat()
	{
		CvMat *I = cvCreateMat(4, 4, CV_32F);
		CV_MAT_ELEM(*I, float,  0, 0) = 1;
		CV_MAT_ELEM(*I, float,  0, 1) = 0;
		CV_MAT_ELEM(*I, float,  0, 2) = 0;
		CV_MAT_ELEM(*I, float,  0, 3) = 0;
		CV_MAT_ELEM(*I, float,  1, 0) = 0;
		CV_MAT_ELEM(*I, float,  1, 1) = 1;
		CV_MAT_ELEM(*I, float,  1, 2) = 0;
		CV_MAT_ELEM(*I, float,  1, 3) = 0;
		CV_MAT_ELEM(*I, float,  2, 0) = 0;
		CV_MAT_ELEM(*I, float,  2, 1) = 0;
		CV_MAT_ELEM(*I, float,  2, 2) = 1;
		CV_MAT_ELEM(*I, float,  2, 3) = 0;
		CV_MAT_ELEM(*I, float,  3, 0) = 0;
		CV_MAT_ELEM(*I, float,  3, 1) = 0;
		CV_MAT_ELEM(*I, float,  3, 2) = 0;
		CV_MAT_ELEM(*I, float,  3, 3) = 1;
		return I;
	}

public:
	Item(void);
	Item(string strFile);
	//Item(string strFile, CvMat *rotationMat, CvMat *translationMat);
	~Item(void);

	void Print(ostream &out);
	
	void InitFeatures();
	bool Connect(Item* pSideItem, CvMat *K, CvMat *D);

	bool GetRotationAngle(float &x, float &y, float &z);

	bool SetFileName(string filename);
	bool SetTransformationMatrix(CvMat *transformationMat);

	string GetFileName() const;
	CvMat* GetTransformationMatrix() const;

	bool IsConnectable(Item* target);
};

