#include "Item.h"
using namespace std;

CvMat *Item::I = Item::GetIdentityMat();

Item::Item(void)
{
	strFileName = "";
	transformationMat = GetIdentityMat();
	imageKeypoints = 0;
	imageKeypoints = 0;
	storage = cvCreateMemStorage(0);
}

Item::Item(string strFile)
{
	strFileName = strFile;
	transformationMat = GetIdentityMat();
	imageKeypoints = 0;
	imageKeypoints = 0;
	storage = cvCreateMemStorage(0);
}

//Item::Item(string strFile, CvMat *rotationMat, CvMat *translationMat)
//{
//	strFileName = strFile;
//	R = cvCreateMat(3, 3, CV_32F);
//	T = cvCreateMat(3, 1, CV_32F);
//
//	cvCopy(rotationMat, R);
//	cvCopy(translationMat, T);
//	objectKeypoints = 0;
//	objectDescriptors = 0;
//	storage = cvCreateMemStorage(0);
//}

Item::~Item(void)
{
	strFileName = "";
	cvReleaseMat(&transformationMat);
	cvReleaseMemStorage(&storage);
}

void Item::Print(ostream &out)
{
	out << this->strFileName << endl;
	///PrintMatrix(this->transformationMat, out);
	//PrintResultMatrix(this->transformationMat, out);
	PrintResultMatrix2(this->transformationMat, out);
}

static CvScalar colors[] = 
    {
        {{0,0,255}},
        {{0,128,255}},
        {{0,255,255}},
        {{0,255,0}},
        {{255,128,0}},
        {{255,255,0}},
        {{255,0,0}},
        {{255,0,255}},
        {{255,255,255}}
    };

void Item::InitFeatures()
{
	char* image_filename = new char[strFileName.length() + 1];
	strcpy(image_filename, strFileName.c_str());
	
	IplImage* object = cvLoadImage( image_filename, CV_LOAD_IMAGE_GRAYSCALE );
    if(!object)
    {
		//"Can not load !!!"
    }     
    CvSURFParams params = cvSURFParams(500, 1);
    cvExtractSURF( object, 0, &imageKeypoints, &imageDescriptors, storage, params );

	cvReleaseImage(&object);
	delete[] image_filename;
}

bool IsSameTransitionVector(float V1x, float V1y, float V2x, float V2y)
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

	if (IsAlmostEqual(fDistance1, fDistance2, DISTANCE_THRES) &&
		IsAlmostEqual(ftanAngle1, ftanAngle2, TAN_ANGLE_THRES) && 
		V1y * V2y >= 0)//loai bo truong hop x_am, y_duong va x_duong, y_am --> 2 truong hop dau van thoa dk
	{
		return true;
	}
	return false;
}

bool Item::IsConnectable(Item* target)
{
	vector<int> ptpairs;
    myfindPairs(target->imageKeypoints, target->imageDescriptors, this->imageKeypoints, this->imageDescriptors, ptpairs ); 

	CvMat *points1 = cvCreateMat(1, ptpairs.size() / 2, CV_32FC2);
	CvMat *points2 = cvCreateMat(1, ptpairs.size() / 2, CV_32FC2);
	for(int i = 0, j = 0; i < (int)ptpairs.size(); i += 2, j++  )
    {
		CvSURFPoint* r1 = (CvSURFPoint*)cvGetSeqElem( this->imageKeypoints, ptpairs[i+1] );
		CvSURFPoint* r2 = (CvSURFPoint*)cvGetSeqElem( target->imageKeypoints, ptpairs[i] );        

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
	bool IsDraw = false;

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
			if (IsSameTransitionVector(x1, y1, x2, y2))
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

		if (IsSameTransitionVector(x1, y1, x2, y2))
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
	if (IsDraw)
	{
		cvNamedWindow("Object Correspond", 1);

		CvScalar colors[] = {{{255,255,255}}};

		IplImage* object = cvLoadImage(this->GetFileName().c_str(), CV_LOAD_IMAGE_GRAYSCALE );
		IplImage* image = cvLoadImage(target->GetFileName().c_str(), CV_LOAD_IMAGE_GRAYSCALE );

		IplImage* object_color = cvCreateImage(cvGetSize(object), 8, 3);
		cvCvtColor( object, object_color, CV_GRAY2BGR );

		CvPoint src_corners[4] = {{0,0}, {object->width,0}, {object->width, object->height}, {0, object->height}};
		CvPoint dst_corners[4];
		IplImage* correspond = cvCreateImage( cvSize(image->width, object->height+image->height), 8, 1 );
		cvSetImageROI( correspond, cvRect( 0, 0, object->width, object->height ) );
		cvCopy( object, correspond );
		cvSetImageROI( correspond, cvRect( 0, object->height, correspond->width, correspond->height ) );
		cvCopy( image, correspond );
		cvResetImageROI( correspond );

		for(int i = 0; i < max_inlier; i++)
		{
			CvPoint2D32f pt2Temp;
			pt2Temp.x = r_pt2[i].x;
			pt2Temp.y = r_pt2[i].y + object->height;
			cvLine(correspond, cvPointFrom32f(r_pt1[i]), cvPointFrom32f(pt2Temp), colors[0]);
		}
		cvShowImage( "Object Correspond", correspond );
		waitKey(0);
		cvDestroyWindow("Object Correspond");
	}

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

// [R|T] to transform item coordinate to the 
bool Item::Connect(Item* pSideItem, CvMat *K, CvMat *D)
{
	if(!IsConnectable(pSideItem))
		return false;

	vector<int> ptpairs;
    myfindPairs(pSideItem->imageKeypoints, pSideItem->imageDescriptors, this->imageKeypoints, this->imageDescriptors, ptpairs ); 

	CvMat *points1 = cvCreateMat(1, ptpairs.size() / 2, CV_32FC2);
	CvMat *points2 = cvCreateMat(1, ptpairs.size() / 2, CV_32FC2);
	for(int i = 0, j = 0; i < (int)ptpairs.size(); i += 2, j++  )
    {
		CvSURFPoint* r1 = (CvSURFPoint*)cvGetSeqElem( this->imageKeypoints, ptpairs[i+1] );
		CvSURFPoint* r2 = (CvSURFPoint*)cvGetSeqElem( pSideItem->imageKeypoints, ptpairs[i] );        

		points1->data.fl[j*2] = r1->pt.x;
		points1->data.fl[j*2 + 1] = r1->pt.y;

		points2->data.fl[j*2] = r2->pt.x;
		points2->data.fl[j*2 + 1] = r2->pt.y;
	}

	CvMat* fundamentalMatrix = cvCreateMat(3,3,CV_32FC1);
	int result = cvFindFundamentalMat(points1, points2, fundamentalMatrix, CV_FM_RANSAC, 1.0, 0.9999);
	if (result == 1) {
		//cout << "Fundamental matrix was found" << endl;
	}
	else {
		cout << "Can't find good fundamental matrix !!!" << endl;
		cvReleaseMat(&points1);
		cvReleaseMat(&points2);
		cvReleaseMat(&fundamentalMatrix);
		return false;
	}

	CvMat *R = NULL;
	CvMat *T = NULL;
	CvMat *P = NULL;
	getRT(K, D, fundamentalMatrix, points1, points2, &R, &T);

	P = CreateTransformationMatrix(R, T);
	pSideItem->SetTransformationMatrix(P);

	if(!IsEqual(this->transformationMat, Item::I))
		cvMatMul(pSideItem->transformationMat, this->transformationMat, pSideItem->transformationMat);

	cvReleaseMat(&P);
	cvReleaseMat(&T);
	cvReleaseMat(&R);
	cvReleaseMat(&fundamentalMatrix);
	cvReleaseMat(&points1);
	cvReleaseMat(&points2);
	return true;
}

bool Item::SetFileName(string filename)
{
	if(filename.length() <= 0)
		return false;
	strFileName = filename;
	return true;
}

bool Item::SetTransformationMatrix(CvMat *transformationMat)
{
	if(!IsTransformationMatrix(transformationMat))
		return false;

	cvCopy(transformationMat, this->transformationMat);
}

string Item::GetFileName() const
{
	return strFileName;
}

CvMat* Item::GetTransformationMatrix() const
{
	return transformationMat;
}