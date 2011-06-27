#pragma once
#include <iostream>
#include <boost/thread.hpp>
#include <boost/date_time.hpp>
#include <string>
#include <sstream>
#include "SynchronisedQueue.h"
#include "ntk/UtilThread.h"
#include <XnLog.h>
#include <XnOS.h>
#include <XnCppWrapper.h>
#include <opencv/cxcore.h>
#include <opencv/cv.h>
#include <opencv/highgui.h>
#include "ntk/geometry/pose_3d.h"
#include <boost/filesystem.hpp> 
#include <string>
#include <iterator>

using namespace xn;
using namespace std;
using namespace boost;
using namespace boost::this_thread;
using namespace boost::filesystem;
using namespace ntk;
using namespace cv;

class ModeRecordGrabberProducer
{
private:
	int m_id;										// The id of the producer
	SynchronisedQueue<RGBDImage *>* m_queue;		// The queue to use
	RGBDImage *m_rgbd_image;
	vector<path> m_image_list;
	int m_current_image_index;
	ntk::RGBDCalibration* m_calib_data;
	bool m_should_exit;
	//RGBDImage *m_rgbd_image;
public:

	// Constructor with id and the queue to use
	ModeRecordGrabberProducer(int id, SynchronisedQueue<RGBDImage *>* queue,
		string strPath)
	{
		m_id=id;
		m_queue=queue;
		m_current_image_index = 0;

		boost::filesystem::path p(strPath); 
		if (is_directory(p))      // is p a directory?
		{
			cout << p << " is a directory containing:\n";

			copy(directory_iterator(p), directory_iterator(), back_inserter(m_image_list));

			sort(m_image_list.begin(), m_image_list.end());             // sort, since directory iteration
			// is not ordered on some file systems

			//for (vector<path>::const_iterator it (m_image_list.begin()); it != m_image_list.end(); ++it)
			//{
			//	cout << "   " << *it << '\n';
			//}
		}
	}

	void setCalibration (ntk::RGBDCalibration* calib_data) { m_calib_data = calib_data; }

	// The thread function fills the queue with data
	void operator () ()
	{
		run();
	}

	void run()
	{

		m_should_exit = false;
		//m_current_image->setCalibration(m_calib_data);
		m_rgbd_image = new RGBDImage();
		m_rgbd_image->setCalibration(m_calib_data);

		while (!m_should_exit)
		{
			//waitForNewEvent();
			boost::this_thread::interruption_point();
			::sleep(boost::posix_time::millisec(500));
			if(!(m_queue->CheckNeedToEnqueue()))
			{
				continue;
			}

			m_rgbd_image->loadFromDir(m_image_list[m_current_image_index].string(), m_calib_data);
			++m_current_image_index;
			if (m_current_image_index >= m_image_list.size())
				m_current_image_index = 0;

			//update va`o queue
			RGBDImage * m_last_image = new RGBDImage();
			m_rgbd_image->copyTo(*m_last_image);
			m_queue->Enqueue(m_last_image);

			// Make sure we can be interrupted
			boost::this_thread::interruption_point();
		}
	}
};
