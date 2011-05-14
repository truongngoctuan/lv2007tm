#include "GetRT.h"
#include "Util.h"
#include <iostream>
using namespace std;

bool myComputeRT2(CvMat *E, CvMat **R1, CvMat **R2, CvMat **T1, CvMat **T2){
	CvMat* W  = cvCreateMat(3,3,CV_32F);
	CvMat *U  = cvCreateMat(3,3,CV_32F);
	CvMat *D  = cvCreateMat(3,3,CV_32F);
	CvMat *Vt = cvCreateMat(3,3,CV_32F);

	//Clear old mat and create new mat
	if(*R1 != NULL)
		cvReleaseMat(R1);
	if(*R2 != NULL)
		cvReleaseMat(R2);
	if(*T1 != NULL)
		cvReleaseMat(T1);
	if(*T2 != NULL)
		cvReleaseMat(T2);

	*R1 = cvCreateMat(3,3,CV_32F);
	*R2 = cvCreateMat(3,3,CV_32F);
	*T1 = cvCreateMat(3,1,CV_32F);
	*T2 = cvCreateMat(3,1,CV_32F);

	int step_U= U->step/sizeof(float);
	int step_T=(*T1)->step/sizeof(float);

	//W
	W->data.fl[0*step_U+0]=0;
	W->data.fl[1*step_U+0]=1;
	W->data.fl[2*step_U+0]=0;

	W->data.fl[0*step_U+1]=-1;
	W->data.fl[1*step_U+1]=0;
	W->data.fl[2*step_U+1]=0;

	W->data.fl[0*step_U+2]=0;
	W->data.fl[1*step_U+2]=0;
	W->data.fl[2*step_U+2]=1;


	cvSVD(E,D,U,Vt,CV_SVD_V_T );

	//Set following matlab
	//Vt->data.fl[0*step_U+0] = co*Vt->data.fl[0*step_U+0];
	//Vt->data.fl[0*step_U+1] = co*Vt->data.fl[0*step_U+1];
	//Vt->data.fl[0*step_U+2] = co*Vt->data.fl[0*step_U+2];

	//Vt->data.fl[1*step_U+0] = co*Vt->data.fl[1*step_U+0];
	//Vt->data.fl[1*step_U+1] = co*Vt->data.fl[1*step_U+1];
	//Vt->data.fl[1*step_U+2] = co*Vt->data.fl[1*step_U+2];

	//Vt->data.fl[2*step_U+0] = co*Vt->data.fl[2*step_U+0];
	//Vt->data.fl[2*step_U+1] = co*Vt->data.fl[2*step_U+1];
	//Vt->data.fl[2*step_U+2] = co*Vt->data.fl[2*step_U+2];

	//**********************************************************
		//R=UWVt or R=UWtVt
		//t= u3 or t=-u3
		//u3 is the third column of U


	//	Calculating rotation matrix R1
	cvMatMul(U,W,*R1);
	cvMatMul(*R1,Vt,*R1);

	double det1 = cvDet(*R1);
	

	//	Calculating rotation matrix R2
	cvTranspose(W,*R2);
	cvMatMul(U,*R2,*R2);
	cvMatMul(*R2,Vt,*R2);

	double det2 = cvDet(*R2);

	//	Calculating vector t1
	(*T1)->data.fl[0*step_T] = U->data.fl[0*step_U+2];
	(*T1)->data.fl[1*step_T] = U->data.fl[1*step_U+2];
	(*T1)->data.fl[2*step_T] = U->data.fl[2*step_U+2];

	//	Calculating vector t2
	(*T2)->data.fl[0*step_T] = -U->data.fl[0*step_U+2];
	(*T2)->data.fl[1*step_T] = -U->data.fl[1*step_U+2];
	(*T2)->data.fl[2*step_T] = -U->data.fl[2*step_U+2];

	cvReleaseMat(&U);
	cvReleaseMat(&D);
	cvReleaseMat(&Vt);
	cvReleaseMat(&W);	

	if(det1 < 0 && det2 < 0)
		return false;
}

void invertSign(CvMat* mat){
	for (int k = 0; k < 3; k++)
	{
		for (int l = 0; l < 3; l++)
		{
			CV_MAT_ELEM( *mat, float,  k, l) = -CV_MAT_ELEM( *mat, float,  k, l);
		}
	}
}

int myComputeRT(CvMat*K, CvMat *F, CvMat **R1, CvMat **R2, CvMat **T1, CvMat **T2)
{
	//Compute essential matrix
	CvMat *E = cvCreateMat(3,3,CV_32F);
	cvTranspose(K,E);
	cvMatMul(E,F,E);
	cvMatMul(E,K,E);

	bool result = myComputeRT2(E, R1, R2, T1, T2);
	if(result == false)
	{
		invertSign(E);
		myComputeRT2(E, R1, R2, T1, T2);
		return -1;
	}
	return 1;
}


int myBestCase(CvMat *K, CvMat *Distortion, CvMat *R1, CvMat *R2, CvMat *T1, CvMat *T2, CvMat *points1, CvMat *points2)
{
	// Vote for 4 solutions 
	double mark[4] = {0,0,0,0};

	// Camera 1 : [R|T] = [I|0]
	// Camera 2 : [R|T] = [R1|T1] -- [R1|T2] -- [R2|T1] -- [R2|T2]
	double cam1Ext_arr[12] =   {1,0,0,0,
								0,1,0,0,
								0,0,1,0};
    CvMat cam1Ext = cvMat(3,4,CV_64F,cam1Ext_arr);


	CvMat *R, *T;
	for(int i = 0; i < 4; i++)
	{
		switch(i){
		case 0:
			R = R1; T = T1; break;
		case 1:
			R = R1; T = T2; break;
		case 2:
			R = R2; T = T1; break;
		case 3:
			R = R2; T = T2; break;
		}

		double rm_a[9] = { 0,0,0, 0,0,0,  0,0,0};
		rm_a[0] = CV_MAT_ELEM( *R, float,  0, 0);
		rm_a[1] = CV_MAT_ELEM( *R, float,  0, 1);
		rm_a[2] = CV_MAT_ELEM( *R, float,  0, 2);
		rm_a[3] = CV_MAT_ELEM( *R, float,  1, 0);
		rm_a[4] = CV_MAT_ELEM( *R, float,  1, 1);
		rm_a[5] = CV_MAT_ELEM( *R, float,  1, 2);
		rm_a[6] = CV_MAT_ELEM( *R, float,  2, 0);
		rm_a[7] = CV_MAT_ELEM( *R, float,  2, 1);
		rm_a[8] = CV_MAT_ELEM( *R, float,  2, 2);

		double tm_a[3] = { 0,0,0};
		tm_a[0] = CV_MAT_ELEM( *T, float,  0, 0);
		tm_a[1] = CV_MAT_ELEM( *T, float,  1, 0);
		tm_a[2] = CV_MAT_ELEM( *T, float,  2, 0);

		// Camera 2 [R|T]
		double cam2Ext_a[12] = {   rm_a[0],rm_a[1],rm_a[2], tm_a[0],
								   rm_a[3],rm_a[4],rm_a[5], tm_a[1],
								   rm_a[6],rm_a[7],rm_a[8], tm_a[2]};
		CvMat cam2Ext = cvMat(3,4,CV_64F,cam2Ext_a);

		// Use triangulation to check if it's a valid solution
		// for each pair of corresponding points : 
		//		vote for this solution if the X is in front of two camera (depth > 0)
		for(int j = 0; j < points1->cols; j++)		
		{
			double x1, y1, x2, y2;
			x1 = points1->data.fl[j*2];		y1 = points1->data.fl[j*2 + 1];
			x2 = points2->data.fl[j*2];		y2 = points2->data.fl[j*2 + 1];

			double pointImg1_a[2] = { x1, y1};
			CvMat pointImg1 = cvMat(1,1,CV_64FC2,pointImg1_a);
			double pointImg2_a[2] = { x2, y2};
			CvMat pointImg2 = cvMat(1,1,CV_64FC2,pointImg2_a);

			cvUndistortPoints(&pointImg1, &pointImg1, K, Distortion);
			cvUndistortPoints(&pointImg2, &pointImg2, K, Distortion);

			//be sure the point's are saved in right matrix format 2xN 1 channel
			CvMat *_pointImg1 = cvCreateMat(2,1,CV_64FC1);
			CvMat *_pointImg2 = cvCreateMat(2,1,CV_64FC1);
			CV_MAT_ELEM( *_pointImg1, double, 0, 0 ) = pointImg1.data.db[0];
			CV_MAT_ELEM( *_pointImg1, double, 1, 0 ) = pointImg1.data.db[1];
			CV_MAT_ELEM( *_pointImg2, double, 0, 0 ) = pointImg2.data.db[0];
			CV_MAT_ELEM( *_pointImg2, double, 1, 0 ) = pointImg2.data.db[1];

			CvMat *point3D = cvCreateMat(4,1,CV_64F) ;
			cvTriangulatePoints(&cam1Ext, &cam2Ext, _pointImg1, _pointImg2, point3D);

			//to get the real position we need to do also a homogeneous division
			point3D->data.db[0] /= point3D->data.db[3];
			point3D->data.db[1] /= point3D->data.db[3];
			point3D->data.db[2] /= point3D->data.db[3];
			point3D->data.db[3] = 1;

			//show the Real point in 3D
			//cout << point3D->data.db[0] << " " << point3D->data.db[1] << " " << point3D->data.db[2] << endl;

			if(point3D->data.db[2] > 0) 
			{
				// Transform the point3D from camera1 coordinate system to camera2 coordinate system
				//		by using the [R|T] matrix to transform it
				CvMat *point2 = cvCreateMat(3, 1, CV_64F);
				cvMatMul(&cam2Ext, point3D, point2);

				//cout << point2->data.db[0] << " " << point2->data.db[1] << " " << point2->data.db[2] << endl;
				if(point2->data.db[2] > 0) 
				{
					// camera1 : depth > 0
					// camera2 : depth > 0
					// +1 vote for this solution
					mark[i]++;
				}

				cvReleaseMat(&point2);
			}

			cvReleaseMat(&_pointImg1);
			cvReleaseMat(&_pointImg2);
			cvReleaseMat(&point3D);
		}
	}

	// get the most voted solution
	int max = -1;
	for(int i = 0 ; i < 4; i++){
		if(max == -1 || mark[i] > mark[max])
			max = i;
	}
	return max;
}

void getRT(CvMat *K, CvMat *Distortion, CvMat *F, CvMat *points1, CvMat *points2, CvMat **R, CvMat **T)
{
	CvMat *R1 = NULL;
	CvMat *R2 = NULL;
	CvMat *T1 = NULL;
	CvMat *T2 = NULL;

	if(R != NULL)
		cvReleaseMat(R);
	if(T != NULL)
		cvReleaseMat(T);

	myComputeRT(K, F, &R1, &R2, &T1, &T2);
	
	int best_case = myBestCase(K, Distortion, R1, R2, T1, T2, points1, points2);
	if(best_case == 0){
		*R = R1;
		*T = T1;
	}
	else if(best_case == 1){
		*R = R1;
		*T = T2;
	}
	else if(best_case == 2){
		*R = R2;
		*T = T1;
	}
	else if(best_case == 3){
		*R = R2;
		*T = T2;
	}
}