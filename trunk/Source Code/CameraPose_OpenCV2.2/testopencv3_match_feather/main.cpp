#include <fstream>
#include <iostream>
#include "ItemManager.h"
#include <vector>
using namespace std;

int main(int argc, char* argv[]) {
	//http://opencv.willowgarage.com/wiki/VisualC%2B%2B_VS2010
	//http://opencv.willowgarage.com/wiki/VisualC%2B%2B
	//config như hướng dẫn, tuy nhiên cần cập nhật theo tên mới
	//link > input >addition dependences: opencv_core220d.lib;opencv_highgui220d.lib;%(AdditionalDependencies)

	int a = 0;
	cout<<"0 calibrate camera (input files: CameraCalibrationListImage1.txt, output files: K1.txt Co1.txt)"<<endl;
	cout<<"1 calculate SURF algorithm for list images, calculate keypoints -> F -> E -> R, t --> write to file (default input files: ListImage.txt K1.txt Co1.txt, ouput files: result1.txt)"<<endl;
	cin>>a;

	switch (a)
	{
	case 0:
		{			
			CvMat *K = cvCreateMat(3, 3, CV_32FC1);
			RotationMatrixUlti::CreateRotationMatrixFromAngle(-0.231766, -14.2694, 2.36591, K);
			CvMat *K2 = cvCreateMat(3, 3, CV_32FC1);
			RotationMatrixUlti::CreateRotationMatrixFromAngle(-0.0837938, -15.0389, 1.728, K2);
			/*
			CV_MAT_ELEM(*K, float,  0, 0) = 0.968353;
			CV_MAT_ELEM(*K, float,  0, 1) = 0.0399885;
			CV_MAT_ELEM(*K, float,  0, 2) = 0.246359;
			CV_MAT_ELEM(*K, float,  1, 0) = -0.0402649;
			CV_MAT_ELEM(*K, float,  1, 1) = 0.999181;
			CV_MAT_ELEM(*K, float,  1, 2) = -0.00391841;
			CV_MAT_ELEM(*K, float,  2, 0) = -0.246314;
			CV_MAT_ELEM(*K, float,  2, 1) = -0.00612539;
			CV_MAT_ELEM(*K, float,  2, 2) = 0.969171;
			PrintMatrix(K);
			*/

			float x, y, z;
			RotationMatrixUlti::CaculateAngleFromRotationMatrix(K, x, y, z);
			cout << x << " " << y << " " << z << endl;

			CvMat *X = cvCreateMat(3, 1, CV_32FC1);
			CV_MAT_ELEM(*X, float,  0, 0) = 0;
			CV_MAT_ELEM(*X, float,  1, 0) = 0;
			CV_MAT_ELEM(*X, float,  2, 0) = 1;

			cvMatMul(K, X, X);
			//cvInvert(K, K);
			cout << "X" << endl;
			PrintMatrix(X);			
			break;
		}
	case 1:
		{
			//lay danh sach file từ ListImage.txt
			vector<string> arrFileName;

			FILE *fptr = fopen("ListImage.txt","r");
			char names[2048];

			while(fscanf(fptr,"%s ",names)==1)
			{
				arrFileName.push_back(names);
			}
			
			ofstream of;
			of.open ("result1.txt");

			ItemManager* pItemManager = ItemManager::CreateItemManager(arrFileName.size(), arrFileName);

			pItemManager->InitFeatures();
			pItemManager->BuildTree();
			pItemManager->Print(of);

			delete pItemManager;
			of.close();
			break;
		}
	default:
		break;
	}
	return 0;
} 
