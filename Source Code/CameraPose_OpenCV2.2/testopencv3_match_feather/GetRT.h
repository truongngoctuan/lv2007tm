#include <cv.h>
#include <highgui.h>
#include <ctype.h>
#include <string>

int myCompute(CvMat*K, CvMat *F, CvMat **R1, CvMat **R2, CvMat **T1, CvMat **T2);
int myBestCase(CvMat *K, CvMat *Distortion, CvMat *R1, CvMat *R2, CvMat *T1, CvMat *T2, CvMat *points1, CvMat *points2);
void getRT(CvMat *K, CvMat *Distortion, CvMat *F, CvMat *points1, CvMat *points2, CvMat **R, CvMat **T);