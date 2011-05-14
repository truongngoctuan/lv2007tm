#include <cv.h>
#include <highgui.h>
#include <stdio.h>
#include <stdlib.h>

void computeRt(int co,CvMat*K, CvMat *F, CvMat **R1, CvMat **R2, CvMat **T1, CvMat **T2);
int best_case(int co,CvMat *K,CvMat *F, CvMat *points1, CvMat *points2,CvMat**R, CvMat **T, CvMat **P0, CvMat **P1);
