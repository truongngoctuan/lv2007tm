#pragma once
#include <iostream>
#include <stdio.h>
#include <boost/thread.hpp>
#include <string>
#include <sstream>
#include "ntk/SynchronisedQueue.h"
#include "ntk/UtilThread.h"
#include <ntk/ntk.h>
#include <ntk/camera/rgbd_frame_recorder.h>
#include <ntk/geometry/relative_pose_estimator.h>
#include <ntk/mesh/surfels_rgbd_modeler.h>

using namespace ntk;
using namespace std;
using namespace boost;
using namespace boost::this_thread;
using namespace cv;

RelativePoseEstimatorFromImage* pose_estimator;
//SurfelsRGBDModeler modeler;
//int iCurrentImageIndex;

//boost::mutex m_mutex; 
boost::mutex mtPoseEstimate;
//boost::mutex mtmodeler;
//boost::mutex mtCurrentImageIndex;

class FindFrameConsumer
{
private:
	int m_id;										// The id of the consumer
	SynchronisedQueue<RGBDImage *>* m_queue;		// The queue to use

	//int m_current_Frame;// dung rieng cho tung thread, dung de cap nhat folder luu file cho tung thread
	//boost::mutex mt;
	RGBDFrameRecorder * m_frame_recorder;
	ntk::RGBDProcessor* m_processor;
public:
	static void Init()
	{
		FeatureSetParams params ("SURF", "SURF64", true);
		pose_estimator = new RelativePoseEstimatorFromImage(params, false);

		//modeler.setMinViewsPerSurfel(1);

		//iCurrentImageIndex = 0;
	}

	//static int GetCurrentImageIndex()
	//{
	//	boost::unique_lock<boost::mutex> lock(mtCurrentImageIndex);
	//	return iCurrentImageIndex;
	//}

	//static void IncCurrentImageIndex()
	//{
	//	boost::unique_lock<boost::mutex> lock(mtCurrentImageIndex);
	//	iCurrentImageIndex++;
	//}

	// Constructor with id and the queue to use.
	FindFrameConsumer(int id, SynchronisedQueue<RGBDImage *>* queue, 
		const char * dir_prefix, int first_index)
	{
		m_id=id;
		m_queue=queue;

		m_frame_recorder = new RGBDFrameRecorder(dir_prefix);
		m_frame_recorder->setFrameIndex(first_index);

		m_processor = new ntk::NiteProcessor();
		m_processor->setFilterFlag(RGBDProcessor::ComputeNormals, 1);
		m_processor->setMaxNormalAngle(90);
		m_processor->setFilterFlag(RGBDProcessor::ComputeMapping, true);
	}

	// The thread function reads data from the queue
	void operator () ()
	{
		int ilast_image;
		Pose3D currentPose;
		bool pose_ok;
		while (true)
		{
			//m_mutex.lock();
			
			RGBDImage * m_last_image = m_queue->Dequeue(ilast_image);
			//m_mutex.unlock();

			TimeCountThread tc_rgbd_process(m_id, "processImage", 2);
			m_processor->processImage(*m_last_image);
			tc_rgbd_process.stop();

			pose_ok = false;
			//mtPoseEstimate.lock();
			TimeCountThread tc_pose_ok(m_id, "pose_ok", 2);
			pose_ok = pose_estimator->estimateNewPose(*m_last_image, currentPose);
			//currentPose = pose_estimator->currentPose();
			//tc_pose_ok.stop();

			//if (pose_ok)
			//{
			//	FindFrameConsumer::IncCurrentImageIndex();
			//	ilast_image = FindFrameConsumer::GetCurrentImageIndex();
			//}
			mtPoseEstimate.unlock();

			if (true)
			{
				//cap nhat currentFrame

				m_frame_recorder->setFrameIndex(ilast_image);
				std::string frame_dir = format("%s/view%04d", 
				m_frame_recorder->directory().absolutePath().toStdString().c_str(), 
				ilast_image);

				string NewFile = format("d:\\test\\color%04d.png", ilast_image);
				//save
				if (m_frame_recorder)
				{
					TimeCountThread tc_saveCurrentFrame(m_id, "saveCurrentFrame", 2);
					m_frame_recorder->saveCurrentFrame(*m_last_image);
					rename((frame_dir + "/raw/color.png").c_str(), NewFile.c_str());
					tc_saveCurrentFrame.stop();
				}

				//{//tao file ply,...
				SurfelsRGBDModeler current_modeler;
				current_modeler.setMinViewsPerSurfel(1);

				TimeCountThread tc_addNewView(m_id, "addNewView", 2);
				current_modeler.addNewView(*m_last_image, currentPose);
				tc_addNewView.stop();

				TimeCountThread tc_computeMesh(m_id, "computeMesh", 2);
				current_modeler.computeMesh();
				tc_computeMesh.stop();

				TimeCountThread tc_saveToPlyFile(m_id, "saveToPlyFile", 2);
				string strDestinationFileName = format("d:\\test\\scene_mesh_%04d.ply", ilast_image);
				current_modeler.currentMesh().saveToPlyFile(strDestinationFileName.c_str());
				tc_saveToPlyFile.stop();
			}

			delete m_last_image;

			// Make sure we can be interrupted
			boost::this_thread::interruption_point();
		}
	}
};
