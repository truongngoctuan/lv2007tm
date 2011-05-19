#pragma once
#include <cv.h>
#include <highgui.h>
#include <ctype.h>
#include <string>
#include <iostream>
#include "RotationMatrixUlti.h"
#include <fstream>
using namespace std;

void PrintMatrix(CvMat *mat);
void PrintMatrix(CvMat *mat, ostream &out);
void PrintResultMatrix(CvMat *mat, ostream &out);
void PrintResultMatrix2(CvMat *mat, ostream &out);
void PrintRotationAngle(CvMat *rotationMatrix);
void PrintRotationAngle(CvMat *rotationMatrix, ostream &out);
bool IsRotationMatrix(CvMat *mat);
bool IsTranslationMatrix(CvMat *mat);
bool IsTransformationMatrix(CvMat *mat);
bool IsEqual(const CvMat *a, const CvMat *b);
CvMat* CreateTransformationMatrix(const CvMat *R, const CvMat *T);

bool IsAlmostEqual(float src, float dest, float SaiSoChoPhep);

#define DEBUG
//http://www.java-samples.com/showtutorial.php?tutorialid=451
#ifndef DEBUG
#define ASSERT(x)
#else

#define ASSERT(message, x) \
	if (! (x)) \
{ \
	cout << "ERROR!! Assert "<<endl; \
	cout << "\tmessage: " << message<<endl; \
	cout << "\ton line " << __LINE__  << endl; \
	cout << "\tin file " << __FILE__ << endl;  \
	WriteErrorLog(message, __LINE__, __FILE__); \
}
#endif

string Str_itoa(int i);
void CLearLogFile();
void WriteLog(const char* logline);
void WriteErrorLog(const char* logline, long line, char* file);