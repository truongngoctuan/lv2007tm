#include <fstream>
#include <iostream>
//#include "ItemManager.h"
#include <vector>
#include "Util.h"
#include <string>
//#include "TestIsConnectable.h"
#include <cv.h>
#include <highgui.h>
#include <ctype.h>
#include <stdio.h>
#include <stdlib.h>
#include "SURFMatching.h"
using namespace std;
using namespace cv;

//using for RANSAC Threshold in IsConnectable function
//#define DISTANCE_THRES 100
//#define TAN_ANGLE_THRES 0.3

bool IsSameTransitionVector2(float V1x, float V1y, float V2x, float V2y, float fDISTANCE_THRES, float fTAN_ANGLE_THRES)
{
	float fDistance1 = sqrt((float)(V1x * V1x + V1y *V1y));
	float fDistance2 = sqrt((float)(V2x * V2x + V2y *V2y));

	float ftanAngle1, ftanAngle2;
	if (IsAlmostEqual(V1x, 0, 0.001))
	{
		if (V1y > 0)
		{
			ftanAngle1 = 1;
		}
		else
		{
			ftanAngle1 = -1;
		}
	}
	else
	{
		ftanAngle1 = V1y / V1x;
	}

	if (IsAlmostEqual(V2x, 0, 0.001))
	{
		if (V2y > 0)
		{
			ftanAngle2 = 1;
		}
		else
		{
			ftanAngle2 = -1;
		}
	}
	else
	{
		ftanAngle2 = V2y / V2x;
	}

	if (IsAlmostEqual(fDistance1, fDistance2, fDISTANCE_THRES) &&
		IsAlmostEqual(ftanAngle1, ftanAngle2, fTAN_ANGLE_THRES) && 
		V1y * V2y >= 0)//loai bo truong hop x_am, y_duong va x_duong, y_am --> 2 truong hop dau van thoa dk
	{
		return true;
	}
	return false;
}

bool Surf(string strImg1, string strImg2, bool bShowResult = true, float fDISTANCE_THRES = 100, float fTAN_ANGLE_THRES = 0.3)
{
	//img1
	string ThisstrFileName = strImg1;
	CvSeq *ThisimageKeypoints;
	CvSeq *ThisimageDescriptors;
	CvMemStorage* Thisstorage;
	Thisstorage = cvCreateMemStorage(0);

	IplImage* object = cvLoadImage(ThisstrFileName.c_str(), CV_LOAD_IMAGE_GRAYSCALE );
    if(!object)
    {
		//"Can not load !!!"
    }     
    CvSURFParams params = cvSURFParams(0, 0);
    cvExtractSURF( object, 0, &ThisimageKeypoints, &ThisimageDescriptors, Thisstorage, params );

	cvReleaseImage(&object);

	//------------------------------------------------------------------
	//img2
	string TargetstrFileName = strImg2;
	CvSeq *TargetimageKeypoints;
	CvSeq *TargetimageDescriptors;
	CvMemStorage* Targetstorage;
	Targetstorage = cvCreateMemStorage(0);

		IplImage* object2 = cvLoadImage(TargetstrFileName.c_str(), CV_LOAD_IMAGE_GRAYSCALE );
    if(!object)
    {
		//"Can not load !!!"
    }     
    CvSURFParams params2 = cvSURFParams(0, 0);
    cvExtractSURF( object2, 0, &TargetimageKeypoints, &TargetimageDescriptors, Targetstorage, params2 );

	cvReleaseImage(&object2);
	//------------------------------------------------------------------

	vector<int> ptpairs;
    myfindPairs(TargetimageKeypoints, TargetimageDescriptors, ThisimageKeypoints, ThisimageDescriptors, ptpairs ); 

	CvMat *points1 = cvCreateMat(1, ptpairs.size() / 2, CV_32FC2);
	CvMat *points2 = cvCreateMat(1, ptpairs.size() / 2, CV_32FC2);
	for(int i = 0, j = 0; i < (int)ptpairs.size(); i += 2, j++  )
    {
		CvSURFPoint* r1 = (CvSURFPoint*)cvGetSeqElem( ThisimageKeypoints, ptpairs[i+1] );
		CvSURFPoint* r2 = (CvSURFPoint*)cvGetSeqElem( TargetimageKeypoints, ptpairs[i] );        

		points1->data.fl[j*2] = r1->pt.x;
		points1->data.fl[j*2 + 1] = r1->pt.y;

		points2->data.fl[j*2] = r2->pt.x;
		points2->data.fl[j*2 + 1] = r2->pt.y;
	}

	//----------------------------------------------------
	//RANSAC here
	unsigned int N = 4000000000;//Near inf
	int sample_count =0;

	int pickedIndex = -1;
	int inlier_number=0;
	int max_inlier = 0;
	int max_inlier_pos= -1;
	int points_number = points1->cols;
	float e;
	float P = 0.99;					//Probability we select at least one set off all inliers
	//bool IsDraw = true;

	//calculate transition vector
	CvMat* TV = cvCreateMat(2,points_number,CV_32F);

	CvPoint2D32f* pt1 = (CvPoint2D32f*)points1->data.fl;
	CvPoint2D32f* pt2 = (CvPoint2D32f*)points2->data.fl;

	for (int i = 0; i < points_number; i++)
	{
		CV_MAT_ELEM(*TV, float,  0, i) = pt1[i].x - pt2[i].x;
		CV_MAT_ELEM(*TV, float,  1, i) = pt1[i].y - pt2[i].y;
	}

	//Determine N- the number of loop
	srand(time(NULL));
	while(sample_count<N)
	{
		inlier_number = 0;
		//pick one
		pickedIndex = rand() % points_number;

		//Count the number of inliers
		for(int i = 0; i < points_number; i++)
		{
			float x1 = CV_MAT_ELEM(*TV, float,  0, pickedIndex);
			float y1 = CV_MAT_ELEM(*TV, float,  1, pickedIndex);
			float x2 = CV_MAT_ELEM(*TV, float,  0, i);
			float y2 = CV_MAT_ELEM(*TV, float,  1, i);
			if (IsSameTransitionVector2(x1, y1, x2, y2, fDISTANCE_THRES, fTAN_ANGLE_THRES))
			{
				inlier_number++;
			}
		}

		e = float(inlier_number)/points_number;
		N = (log(1-P))/(log(1-pow(e,1)));//hinh nhu chua chinh xac

		if (inlier_number > max_inlier)
		{
			max_inlier = inlier_number;
			max_inlier_pos = pickedIndex;
		}

		sample_count++;
	}

	CvMat* ransac_points1 = cvCreateMat(1, max_inlier, CV_32FC2);
	CvMat* ransac_points2 = cvCreateMat(1, max_inlier, CV_32FC2);

	CvPoint2D32f* r_pt1 = (CvPoint2D32f*)ransac_points1->data.fl;
	CvPoint2D32f* r_pt2 = (CvPoint2D32f*)ransac_points2->data.fl;

	int icounter = 0;
	for (int i = 0; i < points_number; i++)
	{
		float x1 = CV_MAT_ELEM(*TV, float,  0, max_inlier_pos);
		float y1 = CV_MAT_ELEM(*TV, float,  1, max_inlier_pos);
		float x2 = CV_MAT_ELEM(*TV, float,  0, i);
		float y2 = CV_MAT_ELEM(*TV, float,  1, i);

		if (IsSameTransitionVector2(x1, y1, x2, y2, fDISTANCE_THRES, fTAN_ANGLE_THRES))
		{
			//add into new arr points
			r_pt1[icounter].x = pt1[i].x;
			r_pt1[icounter].y = pt1[i].y;

			r_pt2[icounter].x = pt2[i].x;
			r_pt2[icounter].y = pt2[i].y;
			icounter++;
		}
	}

	//----------------------------------------------------
	//draw matches points
	if (bShowResult)
	{
		cvNamedWindow("Object Correspond", 1);

		CvScalar colors[] = {{{255,255,255}}};

		IplImage* object = cvLoadImage(ThisstrFileName.c_str(), CV_LOAD_IMAGE_GRAYSCALE );
		IplImage* image = cvLoadImage(TargetstrFileName.c_str(), CV_LOAD_IMAGE_GRAYSCALE );

		IplImage* object_color = cvCreateImage(cvGetSize(object), 8, 3);
		cvCvtColor( object, object_color, CV_GRAY2BGR );

		CvPoint src_corners[4] = {{0,0}, {object->width,0}, {object->width, object->height}, {0, object->height}};
		CvPoint dst_corners[4];
		IplImage* correspond = cvCreateImage( cvSize(image->width + object->width, object->height), 8, 1 );
		cvSetImageROI( correspond, cvRect( 0, 0, object->width, object->height ) );
		cvCopy( object, correspond );
		cvSetImageROI( correspond, cvRect( object->width, 0, correspond->width, correspond->height ) );
		cvCopy( image, correspond );
		cvResetImageROI( correspond );

		for(int i = 0; i < max_inlier; i++)
		{
			CvPoint2D32f pt2Temp;
			pt2Temp.x = r_pt2[i].x + object->width;
			pt2Temp.y = r_pt2[i].y;
			cvLine(correspond, cvPointFrom32f(r_pt1[i]), cvPointFrom32f(pt2Temp), colors[0]);
		}
		cvShowImage( "Object Correspond", correspond );
		waitKey(0);
		cvDestroyWindow("Object Correspond");
	}
	//-------------------------------
	//write to file 
		ofstream m_stream;
	m_stream.open("pairs.txt",ios::out);
	m_stream << max_inlier<<endl;
	for(int i = 0; i < max_inlier; i++)
		{
			CvPoint p1 = cvPointFrom32f(r_pt1[i]);
			CvPoint p2 = cvPointFrom32f(r_pt2[i]);
			m_stream << p1.x << " "<<p1.y<< " "
				<< p2.x << " "<<p2.y<< endl;
		}
	m_stream.close();
	//-------------------------------
	cout<<"max_inlier"<<max_inlier<<"/"<<points_number<<" percent: "<< (float)max_inlier / (float)points_number<<endl;
	TRACKING(("max_inlier" + Str_itoa(max_inlier) + "/" + Str_itoa(points_number)).c_str());
	if ( max_inlier >= 8)
	{
		cout<<"connectable"<<endl;
		TRACKING("connectable");
		return true;
	}
	else
	{
		cout<<"not connectable"<<endl;
		TRACKING("not connectable");
		return false;
	}
}
int main(int argc, char* argv[]) {
	//http://opencv.willowgarage.com/wiki/VisualC%2B%2B_VS2010
	//http://opencv.willowgarage.com/wiki/VisualC%2B%2B
	//config như hướng dẫn, tuy nhiên cần cập nhật theo tên mới
	//link > input >addition dependences: opencv_core220d.lib;opencv_highgui220d.lib;%(AdditionalDependencies)
	try
	{
		if(argc == 3)
		{
			Surf(argv[1], argv[2]);
		}
		else if (argc == 6)
		{
			Surf(argv[1], argv[2], atoi(argv[3]), atof(argv[4]), atof(argv[5]));
		}
		else
		{
			cout<<"no argc matched"<<endl;
		}
	}
	catch(string str)
	{
		cout<<str<<endl;
	}
} 
