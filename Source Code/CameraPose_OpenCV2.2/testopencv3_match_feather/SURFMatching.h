#include <cv.h>
#include <highgui.h>
#include <ctype.h>
#include <stdio.h>
#include <stdlib.h>
#include <string>

int surfMatching(std::string observed, std::string model, CvMat* &observedPoints, CvMat* &modelPoints);
void myfindPairs(const CvSeq* objectKeypoints, const CvSeq* objectDescriptors,
           const CvSeq* imageKeypoints, const CvSeq* imageDescriptors, vector<int>& ptpairs );