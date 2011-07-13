#pragma once
#include <iostream>
#include <stdio.h>
#include <boost/thread.hpp>
#include <string>
#include <sstream>
#include "ntk/SynchronisedQueue.h"
#include "ntk/UtilThread.h"
//#include <ntk/ntk.h>
#include <ntk/camera/rgbd_frame_recorder.h>
#include <ntk/geometry/relative_pose_estimator.h>
#include <ntk/mesh/surfels_rgbd_modeler.h>
#include <ntk/utils/time.h>
#include <ntk/camera/rgbd_processor.h>
#include <fstream>
#include <vector>

using namespace ntk;
using namespace std;
using namespace boost;
using namespace boost::this_thread;
using namespace cv;

//fix loi multi def
//http://msdn.microsoft.com/en-us/library/72zdcz6f%28v=vs.71%29.aspx
//http://cubicspot.blogspot.com/2007/06/solving-pesky-lnk2005-errors.html
RelativePoseEstimatorFromImage* pose_estimator;
SurfelsRGBDModeler current_modeler;
int iCurrentImageIndex;

//boost::mutex m_mutex; 
boost::mutex mtPoseEstimate;
boost::mutex mtmodeler;
boost::mutex mtCurrentImageIndex;
class FindFrameConsumer
{
//public:
//	FindFrameConsumer* pData;
public:
	void RunThread();
	static void do_thread(void* param) {
        static_cast<FindFrameConsumer*>(param)->RunThread();
    }

private:
	int m_id;										// The id of the consumer
	SynchronisedQueue<RGBDImage *>* m_queue;		// The queue to use

	//int m_current_Frame;// dung rieng cho tung thread, dung de cap nhat folder luu file cho tung thread
	//boost::mutex mt;
	RGBDFrameRecorder * m_frame_recorder;
	ntk::RGBDProcessor* m_processor;

	bool m_bIsSaveRawData;
	bool m_bIsSaveMappedData;

	enum Flags {
		NotDecreaseSameVertex = 0x1,
		DecreaseSameVertex = 0x2,
		Notprocess = 0x4,
		SaveFinalPly = 0x8
	};
	int m_iSavePlyMode;
	

	string m_strDestinationFolder;
	string m_strRecordedFolderData;
	string m_strPathCalibrationData;
	string m_strDestinationFolderTemp;

	bool m_bSavePairs;

	bool m_bUseICP;

	vector<string> m_vtFileNameNotDecrease;
public:
	static void Init()
	{
		FeatureSetParams params ("SURF", "SURF64", true);
		pose_estimator = new RelativePoseEstimatorFromImage(params, false);

		current_modeler.setMinViewsPerSurfel(1);

		//iCurrentImageIndex = 0;
	}

	static int GetCurrentImageIndex()
	{
		boost::unique_lock<boost::mutex> lock(mtCurrentImageIndex);
		return iCurrentImageIndex;
	}

	static void IncCurrentImageIndex()
	{
		boost::unique_lock<boost::mutex> lock(mtCurrentImageIndex);
		iCurrentImageIndex++;
	}

	// Constructor with id and the queue to use.
	FindFrameConsumer(int id, SynchronisedQueue<RGBDImage *>* queue, 
		const char * dir_prefix, int first_index)
	{
		SetPause(false);
		m_id=id;
		m_queue=queue;

		m_frame_recorder = new RGBDFrameRecorder(dir_prefix);
		m_frame_recorder->setFrameIndex(first_index);
		//m_frame_recorder->setSaveOnlyRaw(false);

		m_processor = new ntk::NiteProcessor();
		//m_processor = new ntk::KinectProcessor();
		m_processor->setFilterFlag(RGBDProcessor::ComputeNormals, 1);
		m_processor->setMaxNormalAngle(90);
		m_processor->setFilterFlag(RGBDProcessor::ComputeMapping, true);
		//m_processor->setFilterFlag(RGBDProcessor::UndistortImages, true);
		////m_processor->setFilterFlag(RGBDProcessor::NiteProcessor, false);

		m_iSavePlyMode = 0x0;
		//pData = this;
	}

	// The thread function reads data from the queue
	//void operator () ();
	
	void SaveFilePly(SurfelsRGBDModeler& modeler,
		RGBDImage * m_last_image, int ilast_image, Pose3D currentPose, 
		string strFileName, string strTempFileName);
	void SavePairs(int closest_view_index, string strFileName,
								  std::vector<cv::Point3f> ref_points, std::vector<cv::Point3f> img_points);

	void SetSaveRawData(bool b) {m_bIsSaveRawData = b;}
	void SetSaveMappedData(bool b) {m_bIsSaveMappedData = b;}

	bool IsSaveRawData() {return m_bIsSaveRawData;}
	bool IsSaveMappedData() {return m_bIsSaveMappedData;}

	void SetSaveFilePlyMode(Flags flag, bool enabled)
	{ if (enabled) m_iSavePlyMode |= flag; else m_iSavePlyMode &= ~flag; }
	bool hasFilterFlag(Flags flag) const { return m_iSavePlyMode&flag; }
	void setFilterFlags(int flags) { m_iSavePlyMode = flags; }

	void SetDestinationFolder(string str) {m_strDestinationFolder = str;}
	void SetDestinationFolderTemp(string str) {m_strDestinationFolderTemp = str;}
	void SetRecordedFolderData(string str) {m_strRecordedFolderData = str;}
	void SetPathCalibrationData(string str) {m_strPathCalibrationData = str;}

	string GetDestinationFolder() {return m_strDestinationFolder;}
	string GetDestinationFolderTemp() {return m_strDestinationFolderTemp;}
	string GetRecordedFolderData() {return m_strRecordedFolderData;}
	string GetPathCalibrationData() {return m_strPathCalibrationData;}

	void SetSavePairs(bool b) {m_bSavePairs = b;}
	bool IsSavePairs() {return m_bSavePairs;}

	void SetUseICP(bool b) {m_bUseICP = b;}
	bool IsUseICP() {return m_bUseICP;}

	void SaveFileTotalNotDecreaseSameVertex(string strName);

	private:
		bool Pause;
		boost::mutex mtPause;

		public:
	bool IsPause()
	{
		boost::unique_lock<boost::mutex> lock(mtPause);
		return Pause;
	}
	void SetPause(bool b)
	{
		boost::unique_lock<boost::mutex> lock(mtPause);
		Pause = b;
		
	}
};
