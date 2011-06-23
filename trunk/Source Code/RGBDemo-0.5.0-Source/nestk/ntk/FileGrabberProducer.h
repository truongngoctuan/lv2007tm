#pragma once
#include <iostream>
#include <boost/thread.hpp>
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
#include "ntk/camera/nite_rgbd_grabber_internals.hxx"
#include "ntk/geometry/pose_3d.h"

//#include <ntk/ntk.h>

using namespace xn;
using namespace std;
using namespace boost;
using namespace boost::this_thread;
using namespace ntk;
using namespace cv;

namespace ntk
{
// Class that produces objects and puts them in a queue
class FileGrabberProducer
{
private:
	int m_id;										// The id of the producer
	SynchronisedQueue<RGBDImage *>* m_queue;		// The queue to use

	  
  //xn::Context m_ni_context;
  //xn::DepthGenerator m_ni_depth_generator;
  //xn::ImageGenerator m_ni_rgb_generator;
  //xn::UserGenerator m_ni_user_generator;
  bool m_need_pose_to_calibrate;
  XnChar m_calibration_pose[20];
  int m_max_num_users;
  //BodyEventDetector* m_body_event_detector;
  bool m_high_resolution;
  bool m_custom_bayer_decoding;
  bool m_trackUser;

  ntk::RGBDCalibration* m_calib_data;
  
  bool m_should_exit;
  uint64 m_last_frame_tick;
  double m_framerate;
  int m_frame_count;

public:

	// Constructor with id and the queue to use
	FileGrabberProducer(int id, SynchronisedQueue<RGBDImage *>* queue)
	{
		m_id=id;
		m_queue=queue;

		m_high_resolution = false;
		m_rgbd_image = new RGBDImage();
		m_current_image = new RGBDImage();
		m_trackUser = false;
		m_custom_bayer_decoding = true;
	}

	// The thread function fills the queue with data
	void operator () ()
	{
		run();
	}

	void check_error(const XnStatus& status, const char* what) const;
	void initialize();
	void estimateCalibration();
	void run();

	RGBDImage *m_rgbd_image;
	RGBDImage *m_current_image;
};
}