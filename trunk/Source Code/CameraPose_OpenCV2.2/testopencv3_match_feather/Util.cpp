#include "Util.h"
#include <iostream>
using namespace std;

void PrintMatrix(CvMat *mat)
{
	for (int i = 0; i < mat->rows; i++)
	{
		cout << "   ";
		for (int j = 0; j < mat->cols; j++)
		{
			cout << CV_MAT_ELEM( *mat, float,  i, j) << "\t";
		}
		cout << endl;
	}
}

void PrintMatrix(CvMat *mat, ostream &out)
{
	for (int i = 0; i < mat->rows; i++)
	{
		//out << "   ";
		for (int j = 0; j < mat->cols; j++)
		{
			out << CV_MAT_ELEM( *mat, float,  i, j) << " ";
		}
		out << endl;
	}
}

void PrintResultMatrix(CvMat *mat, ostream &out)
{
	CvMat *transposeMat = cvCreateMat(mat->cols, mat->rows, mat->type);
	cvTranspose(mat, transposeMat);
	for (int i = 0; i < mat->rows; i++)
	{
		//out << "   ";
		for (int j = 0; j < mat->cols; j++)
		{
			out << CV_MAT_ELEM( *transposeMat, float,  i, j) << " ";
		}
		out << endl;
	}
	cvReleaseMat(&transposeMat);
}

// Input : transformation matrix [R|T] from sideCam to mainCam, outstream
// Output : - invert [R|T] => mainCam to sideCam
//			- invert Ry, Rz, Ty, Tz : to suit with Silverlight Coordinate System (x : right, y : up, z : into)
//			- create new [R|T]
//			- transpose [R|T] : to suit with affine matrix in Silverlight
//			- output

void PrintResultMatrix2(CvMat *mat, ostream &out)
{
	if(mat->rows != 4 || mat->cols != 4)
		return;
	// Extract R, T
	CvMat* R = cvCreateMat(3, 3, CV_32F);
	CV_MAT_ELEM( *R, float,  0, 0) = CV_MAT_ELEM(*mat, float,  0, 0);
	CV_MAT_ELEM( *R, float,  0, 1) = CV_MAT_ELEM(*mat, float,  0, 1);
	CV_MAT_ELEM( *R, float,  0, 2) = CV_MAT_ELEM(*mat, float,  0, 2);
	CV_MAT_ELEM( *R, float,  1, 0) = CV_MAT_ELEM(*mat, float,  1, 0);
	CV_MAT_ELEM( *R, float,  1, 1) = CV_MAT_ELEM(*mat, float,  1, 1);
	CV_MAT_ELEM( *R, float,  1, 2) = CV_MAT_ELEM(*mat, float,  1, 2);
	CV_MAT_ELEM( *R, float,  2, 0) = CV_MAT_ELEM(*mat, float,  2, 0);
	CV_MAT_ELEM( *R, float,  2, 1) = CV_MAT_ELEM(*mat, float,  2, 1);
	CV_MAT_ELEM( *R, float,  2, 2) = CV_MAT_ELEM(*mat, float,  2, 2);

	CvMat* T = cvCreateMat(3, 1, CV_32F);
	CV_MAT_ELEM( *T, float,  0, 0) = CV_MAT_ELEM(*mat, float,  0, 3);
	CV_MAT_ELEM( *T, float,  1, 0) = CV_MAT_ELEM(*mat, float,  1, 3);
	CV_MAT_ELEM( *T, float,  2, 0) = CV_MAT_ELEM(*mat, float,  2, 3);

	// invert [R|T] => mainCam to sideCam
	cvInvert(R, R);
	CV_MAT_ELEM( *T, float,  0, 0) = -CV_MAT_ELEM(*T, float,  0, 0);
	CV_MAT_ELEM( *T, float,  1, 0) = -CV_MAT_ELEM(*T, float,  1, 0);
	CV_MAT_ELEM( *T, float,  2, 0) = -CV_MAT_ELEM(*T, float,  2, 0);

	PrintRotationAngle(R, out);

	// invert Ry, Rz, Ty, Tz : to suit with Silverlight Coordinate System (x : right, y : up, z : into)
	float AngleX, AngleY, AngleZ;
	RotationMatrixUlti::CaculateAngleFromRotationMatrix(R, AngleX, AngleY, AngleZ);
	AngleY = -AngleY;
	AngleZ = -AngleZ;
	RotationMatrixUlti::CreateRotationMatrixFromAngle(AngleX, AngleY, AngleZ, R);

	//CV_MAT_ELEM( *T, float,  0, 0) = -CV_MAT_ELEM(*T, float,  0, 0);
	CV_MAT_ELEM( *T, float,  1, 0) = -CV_MAT_ELEM(*T, float,  1, 0);
	CV_MAT_ELEM( *T, float,  2, 0) = -CV_MAT_ELEM(*T, float,  2, 0);

	// create new [R|T]
	CvMat* resultMat = CreateTransformationMatrix(R, T);

	// transpose [R|T] : to suit with affine matrix in Silverlight
	cvTranspose(resultMat, resultMat);

	// output
	PrintMatrix(resultMat, out);

	cvReleaseMat(&R);
	cvReleaseMat(&T);
	cvReleaseMat(&resultMat);
}

void PrintRotationAngle(CvMat *rotationMatrix)
{
	if(rotationMatrix->cols != 3 || rotationMatrix->rows != 3)
		return;

	float AngleX, AngleY, AngleZ;

	RotationMatrixUlti::CaculateAngleFromRotationMatrix(rotationMatrix, AngleX, AngleY, AngleZ);

	cout << "Angle: " << endl 
				<< "   " << AngleX << " " << AngleY << " " << AngleZ << endl;
}

void PrintRotationAngle(CvMat *rotationMatrix, ostream &out)
{
	if(rotationMatrix->cols != 3 || rotationMatrix->rows != 3)
		return;

	float AngleX, AngleY, AngleZ;
	RotationMatrixUlti::CaculateAngleFromRotationMatrix(rotationMatrix, AngleX, AngleY, AngleZ);
	out << "Angle: " << endl 
				<< "   " << AngleX << " " << AngleY << " " << AngleZ << endl;
}

const int EPSILON = 0.00001;
bool IsRotationMatrix(CvMat *R)
{
	if(R->cols == 3 && R->rows == 3)
	{
		if(abs(cvDet(R)) < EPSILON)
			return true;
	}
	return false;
}

bool IsTranslationMatrix(CvMat *T)
{
	if(T->cols == 1 && T->rows == 3)
	{
		return true;
	}
	return false;
}

bool IsTransformationMatrix(CvMat *mat)
{
	if(mat == NULL)
		return false;
	if(mat->rows != 4 || mat->cols != 4)
		return false;
	return true;
}

bool IsEqual(const CvMat *a, const CvMat *b)
{
	if(a->rows != b->rows || a->cols != b->cols)
		return false;
	for(int row = 0; row < a->rows; row++)
	{
		for(int col = 0; col < a->cols; col++)
		{
			if(CV_MAT_ELEM(*a, float, row, col) != CV_MAT_ELEM(*b, float, row, col))
				return false;
		}
	}
	return true;
}

CvMat* GetAffineTranslateMat(const CvMat *T)
{
	CvMat *mat = cvCreateMat(3, 3, CV_32F);
	CV_MAT_ELEM(*mat, float,  2, 0) = CV_MAT_ELEM(*T, float, 0, 0);
	CV_MAT_ELEM(*mat, float,  2, 1) = CV_MAT_ELEM(*T, float, 1, 0);
	CV_MAT_ELEM(*mat, float,  2, 2) = CV_MAT_ELEM(*T, float, 2, 0);
	return mat;
}

CvMat* CreateTransformationMatrix(const CvMat *R, const CvMat *T)
{
	// ProjectionMatrix [R|T]
	CvMat *P = cvCreateMat(4, 4, CV_32F);
	CV_MAT_ELEM(*P, float,  0, 0) = CV_MAT_ELEM(*R, float, 0, 0);
	CV_MAT_ELEM(*P, float,  0, 1) = CV_MAT_ELEM(*R, float, 0, 1);
	CV_MAT_ELEM(*P, float,  0, 2) = CV_MAT_ELEM(*R, float, 0, 2);
	CV_MAT_ELEM(*P, float,  1, 0) = CV_MAT_ELEM(*R, float, 1, 0);
	CV_MAT_ELEM(*P, float,  1, 1) = CV_MAT_ELEM(*R, float, 1, 1);
	CV_MAT_ELEM(*P, float,  1, 2) = CV_MAT_ELEM(*R, float, 1, 2);
	CV_MAT_ELEM(*P, float,  2, 0) = CV_MAT_ELEM(*R, float, 2, 0);
	CV_MAT_ELEM(*P, float,  2, 1) = CV_MAT_ELEM(*R, float, 2, 1);
	CV_MAT_ELEM(*P, float,  2, 2) = CV_MAT_ELEM(*R, float, 2, 2);	

	CV_MAT_ELEM(*P, float,  0, 3) = CV_MAT_ELEM(*T, float, 0, 0);
	CV_MAT_ELEM(*P, float,  1, 3) = CV_MAT_ELEM(*T, float, 1, 0);
	CV_MAT_ELEM(*P, float,  2, 3) = CV_MAT_ELEM(*T, float, 2, 0);

	CV_MAT_ELEM(*P, float,  3, 0) = 0;
	CV_MAT_ELEM(*P, float,  3, 1) = 0;
	CV_MAT_ELEM(*P, float,  3, 2) = 0;
	CV_MAT_ELEM(*P, float,  3, 3) = 1;

	return P;
}

bool IsAlmostEqual(float src, float dest, float SaiSoChoPhep)
{
	if (dest - SaiSoChoPhep <= src && src <= dest + SaiSoChoPhep)
	{
		return true;
	}
	return false;
}
