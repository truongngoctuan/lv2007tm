#pragma once
#include <string>
#include <vector>
using namespace std;
//using namespace cv;

class UltiRawStandardDepth
{
public:
	UltiRawStandardDepth(void);
	~UltiRawStandardDepth(void);

	void setRawDepth(cv::Mat1f rawDepth);
	void setStandardDepth(vector<vector<int>> stDepth);

	cv::Mat1f getRawDepth();
	vector<vector<int>> getStandardDepth();
	
	void rawToStandardDepth();
	void standardToRawDepth();

	void saveRawDepthToFile(string strFileName);
	void saveStandardDepthToFile(string strFileName);

	void loadRawDepthFromFile(string strFileName);
	void loadStandardDepthFromFile(string strFileName);
private:
	cv::Mat1f rawDepth;
	vector<vector<int>> stDepth;
};
