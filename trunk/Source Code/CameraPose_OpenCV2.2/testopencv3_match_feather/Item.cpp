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

bool Item::IsConnectable(Item* target)
{
	return true;
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
		cvMul(this->transformationMat, pSideItem->transformationMat, pSideItem->transformationMat);

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