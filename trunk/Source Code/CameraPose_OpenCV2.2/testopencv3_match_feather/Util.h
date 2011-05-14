#include <cv.h>
#include <highgui.h>
#include <ctype.h>
#include <string>
#include <iostream>
#include "RotationMatrixUlti.h"
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