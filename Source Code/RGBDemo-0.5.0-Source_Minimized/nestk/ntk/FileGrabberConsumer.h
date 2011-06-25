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
#include <ntk/camera/rgbd_processor.h>
#include <ntk/utils/time.h>

using namespace ntk;
using namespace std;
using namespace boost;
using namespace boost::this_thread;
using namespace cv;
boost::mutex m_mutex; 
class FileGrabberConsumer
{
private:
	int m_id;										// The id of the consumer
	SynchronisedQueue<RGBDImage *>* m_queue;		// The queue to use
	
	//int m_current_Frame;// dung rieng cho tung thread, dung de cap nhat folder luu file cho tung thread
	//boost::mutex mt;
	  RGBDFrameRecorder * m_frame_recorder;
 ntk::RGBDProcessor* m_processor;

public:
	// Constructor with id and the queue to use.
	FileGrabberConsumer(int id, SynchronisedQueue<RGBDImage *>* queue, 
		const char * dir_prefix, int first_index)
	{
		m_id=id;
		m_queue=queue;

		m_frame_recorder = new RGBDFrameRecorder(dir_prefix);
		m_frame_recorder->setFrameIndex(first_index);

		m_processor = new ntk::NiteProcessor();
		
	}

	// The thread function reads data from the queue
	void operator () ()
	{
		while (true)
		{
			// Get the data from the queue and print it
			//cout<<"Consumer "<<UtilThread::IntToString(m_id).c_str()
			//	<<" consumed: ("<<m_queue->Dequeue().c_str();

			m_mutex.lock();
			int ilast_image;
			RGBDImage * m_last_image = m_queue->Dequeue(ilast_image);
			//cap nhat currentFrame
			
			m_frame_recorder->setFrameIndex(ilast_image);
			std::string frame_dir = format("%s/view%04d", 
				m_frame_recorder->directory().c_str(), 
				ilast_image);
			string NewFile = format("d:\\test\\color%04d.png", ilast_image);

			m_mutex.unlock();

			TimeCount tc_rgbd_process("m_processor.processImage", 2);
			m_processor->processImage(*m_last_image);
			tc_rgbd_process.stop();

			if (m_frame_recorder)
			{
				m_frame_recorder->saveCurrentFrame(*m_last_image);
				rename((frame_dir + "/raw/color.png").c_str(), NewFile.c_str());
			}

			delete m_last_image;

			// Make sure we can be interrupted
			boost::this_thread::interruption_point();
		}
	}
};
