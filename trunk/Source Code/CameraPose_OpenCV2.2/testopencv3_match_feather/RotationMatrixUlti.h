#pragma once
#include <cv.h>
#include <highgui.h>
#include <stdio.h>
#include <stdlib.h>
#include <iostream>
using namespace std;
class RotationMatrixUlti
{
public:
	RotationMatrixUlti(void);
	~RotationMatrixUlti(void);
	//rotation matrix x = ψ; y = θ; z = φ;
	//angle (độ) --> rotation matrix3x3
	static void CreateRotationMatrixFromAngle( float AngleX, float AngleY, float AngleZ, CvMat *dest);
	//rotation matrix3x3 --> angle (độ)
	static void CaculateAngleFromRotationMatrix(const CvMat *src, float &AngleX, float &AngleY, float &AngleZ);

	static float ConvertToRadian(float fAngle);
	static float ConvertTo360(float fAngle);


	//Mat Mx = (Mat_<float>(3,3) << 1, 0, 0,
	//	0, cos(alphaX), sin(alphaX),
	//	0, -sin(alphaX), cos(alphaX));	

	//Mat My = (Mat_<float>(3,3) << cos(alphaY), 0, sin(alphaY),
	//	0, 1, 0,
	//	-sin(alphaY), 0, cos(alphaY));

	//Mat Mz = (Mat_<float>(3,3) << cos(alphaZ), sin(alphaZ), 0,
	//	-sin(alphaZ), cos(alphaZ), 0, 
	//	0, 0, 1);
};

