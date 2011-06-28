#pragma once
#include <string>
#include <fstream>
#include <vector>
#include <ntk/core.h>

using namespace std;
using namespace cv;

int EPSILON = 1e-4;
bool isAlmostEqual(float a, float b)
{
	if(abs(a - b) > EPSILON)
		return false;
	return true;
}

bool edgeAlmostEqual(cv::Point3f p1a, cv::Point3f p1b, cv::Point3f p2a, cv::Point3f p2b)
{
	if(!isAlmostEqual(p1a.x - p1b.x, p2a.x - p2b.x))
		return false;
	if(!isAlmostEqual(p1a.y - p1b.y, p2a.y - p2b.y))
		return false;
	if(!isAlmostEqual(p1a.z - p1b.z, p2a.z - p2b.z))
		return false;
	return true;
}

bool InitFeaturePairs(const std::vector<cv::Point3f>& pFix,
	const std::vector<cv::Point3f>& pMove)
{
	EPSILON = 10;
	int num = pFix.size();

	// choose best pairs
	// get 4 best pairs
	int index1, index2, index3, index4;
	index1 = index2 = index3 = index4 = -1;
	bool found = false;
	for(int i1 = 0; i1 < num; i1++)
	{
		for(int i2 = 0; i2 < num; i2++)
		{
			if(i2 == i1)
				continue;

			if(!edgeAlmostEqual(pFix[i2], pFix[i1], pMove[i2], pMove[i1]))
				continue;
			for(int i3 = 0; i3 < num; i3++)
			{
				if(i3 == i1 || i3 == i2)
					continue;

				if(!edgeAlmostEqual(pFix[i3], pFix[i1], pMove[i3], pMove[i1]))
					continue;
				/*if(!edgeAlmostEqual(pFix[i3], pFix[i2], pMove[i3], pMove[i2]))
					continue;*/
				for(int i4 = 0; i4 < num; i4++)
				{
					if(i4 == i1 || i4 == i2 || i4 == i3)
						continue;

					if(!edgeAlmostEqual(pFix[i4], pFix[i1], pMove[i4], pMove[i1]))
						continue;
					/*if(!edgeAlmostEqual(pFix[i4], pFix[i2], pMove[i4], pMove[i2]))
						continue;
					if(!edgeAlmostEqual(pFix[i4], pFix[i3], pMove[i4], pMove[i3]))
						continue;*/

					found = true;
					if(found)
					{
						index1 = i1;
						index2 = i2;
						index3 = i3;
						index4 = i4;
						break;
					}
				}
				if(found)
						break;
			}
			if(found)
						break;
		}
		if(found)
						break;
	}
	return found;
}