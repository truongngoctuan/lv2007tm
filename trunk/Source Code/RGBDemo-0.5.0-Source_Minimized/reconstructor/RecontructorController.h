#pragma once
#include <iostream>
#include <stdio.h>
#include <stdlib.h>
#include <cstdlib>
#include <sstream>
#include <iomanip>

#include <boost/thread.hpp>
#include <string>
#include <sstream>
#include <ntk/SynchronisedQueue.h>
#include <ntk/FileGrabberProducer.h>
#include <ntk/FindFrameConsumer.h>
#include <ntk/ModeRecordGrabberProducer.h>

using namespace std;
using namespace boost;
using namespace boost::this_thread;
using namespace ntk;
using namespace cv;

//how to use thread in boost library
//http://www.quantnet.com/cplusplus-multithreading-boost/
//http://en.highscore.de/cpp/boost/

//how to fix error when linking to thread boost library
//https://svn.boost.org/trac/boost/ticket/2226
namespace boost {
	struct thread::dummy {};
}

class RecontructorController
{
public:
		enum Flags {
		NotDecreaseSameVertex = 0x1,
		DecreaseSameVertex = 0x2,
		Notprocess = 0x4
		//SaveFinalPly = 0x8
	};
	//từ kineck/từ file --> save/ko save data
	//save data gồm raw và mapped
	//xuất ra ply chưa bỏ trùng/đã bỏ trùng/chưa hề align
	//xuất ra pairs 3d cho frame đó
	//có xuất kết quả ply tổng hợp cuối cùng
	//có dùng thêm icp
private:
	bool m_bIsFromKineck;
	bool m_bIsSaveRawData;
	bool m_bIsSaveMappedData;


	int m_iSavePlyMode;

	bool m_bSavePairs;
	bool m_bSaveFinalPly;
	bool m_bUseICP;

	//get arg data
	//1. destination folder data, we will create a temperate folder to save data 
	//		before copy to this folder
	//2. recorded folder data, in this mode, do not save data back
	//3. path of calibration data
	string m_strDestinationFolder;
	string m_strRecordedFolderData;
	string m_strPathCalibrationData;

public: 
	void SetLoadDataFromKineck(bool b) {
		m_bIsFromKineck = b;
		if (m_bIsFromKineck)
		{
			SetSaveRawData(true);
			SetSaveMappedData(false);
		}
		else
		{
			SetSaveRawData(false);
			SetSaveMappedData(false);
		}
	}

	void SetSavePairs(bool b) {m_bSavePairs = b;}

	//normal 
	//noneed, setup in upper function
	void SetSaveRawData(bool b) {m_bIsSaveRawData = b;}
	void SetSaveMappedData(bool b) {m_bIsSaveMappedData = b;}
	void SetSaveFilePlyMode(Flags flag, bool enabled)
	{ if (enabled) m_iSavePlyMode |= flag; else m_iSavePlyMode &= ~flag; }

	void SetDestinationFolder(string str) {m_strDestinationFolder = str;}
	void SetRecordedFolderData(string str) {m_strRecordedFolderData = str;}
	void SetPathCalibrationData(string str) {m_strPathCalibrationData = str;}
public:
	RecontructorController(void);
	~RecontructorController(void);

	void GetArgData(char argc, char** argv);
	void Run();
	void RunFromKineck();
	void RunFromRecordedData();
};
