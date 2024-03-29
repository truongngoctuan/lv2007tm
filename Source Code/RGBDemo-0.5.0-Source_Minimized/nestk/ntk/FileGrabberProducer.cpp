#include "FileGrabberProducer.h"

  xn::Context m_ni_context;
  xn::DepthGenerator m_ni_depth_generator;
  xn::ImageGenerator m_ni_rgb_generator;
  xn::UserGenerator m_ni_user_generator;

void FileGrabberProducer :: check_error(const XnStatus& status, const char* what) const
{
	if (status != XN_STATUS_OK)
	{
		ntk_dbg(0) << "[ERROR] " << cv::format("%s failed: %s\n", what, xnGetStatusString(status));
		ntk_throw_exception("Error in NiteRGBDGrabber.");
		//cout<<"XN_STATUS_NOT_OK"<<endl;
	}
}

void FileGrabberProducer :: initialize()
{
	string config_file = m_strConfigFile;//"NestkConfig.xml";

	xn::EnumerationErrors errors;
	XnStatus status = m_ni_context.InitFromXmlFile(config_file.c_str(), &errors);
	if (status != XN_STATUS_OK)
	{
		ntk_dbg(0) << "[ERROR] " << xnGetStatusString(status);
		ntk_throw_exception("Could not initialize NITE. Check Log."
		                    "Most probable reasons are device not connected or no config/ directory"
		                    "in the current directory.");
	}

	status = m_ni_context.FindExistingNode(XN_NODE_TYPE_DEPTH, m_ni_depth_generator);
	check_error(status, "Find depth generator");
	//sua them
	if(m_trackUser)
	{
		status = m_ni_context.FindExistingNode(XN_NODE_TYPE_USER, m_ni_user_generator);
		check_error(status, "Find user generator");
	}
	status = m_ni_context.FindExistingNode(XN_NODE_TYPE_IMAGE, m_ni_rgb_generator);
	check_error(status, "Find image generator");

	if (m_high_resolution)
	{
		XnMapOutputMode rgb_mode;
		rgb_mode.nFPS = 15;
		rgb_mode.nXRes = 1280;
		rgb_mode.nYRes = 1024;
		m_ni_rgb_generator.SetMapOutputMode(rgb_mode);
	}

	m_custom_bayer_decoding = true;
	if (m_custom_bayer_decoding)
	{
		// Grayscale to get raw Bayer pattern.
		status = m_ni_rgb_generator.SetIntProperty ("InputFormat", 6);
		check_error(status, "Change input format");

		status = m_ni_rgb_generator.SetPixelFormat(XN_PIXEL_FORMAT_GRAYSCALE_8_BIT);
		check_error(status, "Change pixel format");
	}

	ntk_ensure(m_ni_depth_generator.IsCapabilitySupported(XN_CAPABILITY_ALTERNATIVE_VIEW_POINT), "Cannot register images.");
	m_ni_depth_generator.GetAlternativeViewPointCap().SetViewPoint(m_ni_rgb_generator);
	//if(m_trackUser)
	//{
	//	//ntk_throw_exception_if(!m_ni_user_generator.IsCapabilitySupported(XN_CAPABILITY_SKELETON),
	//	//                       "Supplied user generator doesn't support skeleton.");

	//	XnCallbackHandle hUserCallbacks, hCalibrationCallbacks, hPoseCallbacks;
	//	m_ni_user_generator.RegisterUserCallbacks(User_NewUser, User_LostUser, this, hUserCallbacks);
	//	m_ni_user_generator.GetSkeletonCap().RegisterCalibrationCallbacks(UserCalibration_CalibrationStart, UserCalibration_CalibrationEnd, this, hCalibrationCallbacks);

	//	if (m_ni_user_generator.GetSkeletonCap().NeedPoseForCalibration())
	//	{
	//		m_need_pose_to_calibrate = true;
	//		if (!m_ni_user_generator.IsCapabilitySupported(XN_CAPABILITY_POSE_DETECTION))
	//			//ntk_throw_exception("Pose required, but not supported\n");
	//			m_ni_user_generator.GetPoseDetectionCap().RegisterToPoseCallbacks(UserPose_PoseDetected, NULL, this, hPoseCallbacks);
	//		m_ni_user_generator.GetSkeletonCap().GetCalibrationPose(m_calibration_pose);
	//	}

	//	m_ni_user_generator.GetSkeletonCap().SetSkeletonProfile(XN_SKEL_PROFILE_ALL);
	//}
	//ket thuc sua
	//if (m_body_event_detector)
	//	m_body_event_detector->initialize(m_ni_context, m_ni_depth_generator);

	status = m_ni_context.StartGeneratingAll();
	check_error(status, "StartGenerating");

	m_ni_context.WaitAndUpdateAll();
	estimateCalibration();
	//m_calib_data = new RGBDCalibration();
	//m_calib_data->loadFromFile("kinect_calibration.yml");
	//run();
}

void FileGrabberProducer :: estimateCalibration()
{
	XnPoint3D p;
	p.X = 0; p.Y = 0; p.Z = -1;
	m_ni_depth_generator.ConvertProjectiveToRealWorld(1, &p, &p);

	p.X = 0; p.Y = 0; p.Z = -1;
	m_ni_depth_generator.ConvertRealWorldToProjective(1, &p, &p);
	double cx = p.X;
	double cy = p.Y;  

	p.X = 1; p.Y = 1; p.Z = -1;
	m_ni_depth_generator.ConvertRealWorldToProjective(1, &p, &p);

	double fx = -(p.X-cx);
	double fy = p.Y-cy;

	const double f_correction_factor = 528.0/575.8;
	fx *= f_correction_factor;
	fy *= f_correction_factor;

	const double cy_correction_factor = 267.0/240.0;
	cy *= cy_correction_factor;

	m_calib_data = new RGBDCalibration();

	xn::DepthMetaData depthMD;
	m_ni_depth_generator.GetMetaData(depthMD);

	xn::ImageMetaData rgbMD;
	m_ni_rgb_generator.GetMetaData(rgbMD);

	int depth_width = depthMD.XRes();
	int depth_height = depthMD.YRes();

	int rgb_width = rgbMD.XRes();
	int rgb_height = rgbMD.YRes();

	m_calib_data->setRawRgbSize(cv::Size(rgb_width, rgb_height));
	m_calib_data->setRgbSize(cv::Size(rgb_width, rgb_height));
	m_calib_data->raw_depth_size = cv::Size(depth_width, depth_height);
	m_calib_data->depth_size = cv::Size(depth_width, depth_height);

	float width_ratio = float(rgb_width)/depth_width;
	float height_ratio = float(rgb_height)/depth_height;

	float rgb_fx = fx * width_ratio;
	// Pixels are square on a Kinect.
	// Image height gets cropped when going from 1280x1024 in 640x480.
	// The ratio remains 2.
	float rgb_fy = rgb_fx;
	float rgb_cx = cx * width_ratio;
	float rgb_cy = cy * width_ratio;

	m_calib_data->rgb_intrinsics = cv::Mat1d(3,3);
	setIdentity(m_calib_data->rgb_intrinsics);
	m_calib_data->rgb_intrinsics(0,0) = rgb_fx;
	m_calib_data->rgb_intrinsics(1,1) = rgb_fy;
	m_calib_data->rgb_intrinsics(0,2) = rgb_cx;
	m_calib_data->rgb_intrinsics(1,2) = rgb_cy;

	m_calib_data->rgb_distortion = Mat1d(1,5);
	m_calib_data->rgb_distortion = 0.;
	m_calib_data->zero_rgb_distortion = true;

	// After getAlternativeViewpoint, both camera have the same parameters.

	m_calib_data->depth_intrinsics = cv::Mat1d(3,3);
	setIdentity(m_calib_data->depth_intrinsics);
	m_calib_data->depth_intrinsics(0,0) = fx;
	m_calib_data->depth_intrinsics(1,1) = fy;
	m_calib_data->depth_intrinsics(0,2) = cx;
	m_calib_data->depth_intrinsics(1,2) = cy;

	m_calib_data->depth_distortion = Mat1d(1,5);
	m_calib_data->depth_distortion = 0.;
	m_calib_data->zero_depth_distortion = true;

	m_calib_data->R = Mat1d(3,3);
	setIdentity(m_calib_data->R);

	m_calib_data->T = Mat1d(3,1);
	m_calib_data->T = 0.;

	m_calib_data->depth_pose = new Pose3D();
	m_calib_data->depth_pose->setCameraParametersFromOpencv(m_calib_data->depth_intrinsics);

	m_calib_data->rgb_pose = new Pose3D();
	m_calib_data->rgb_pose->toRightCamera(m_calib_data->rgb_intrinsics,
		m_calib_data->R,
		m_calib_data->T);
}

void FileGrabberProducer :: run()
{
	m_should_exit = false;
	m_current_image->setCalibration(m_calib_data);
	m_rgbd_image->setCalibration(m_calib_data);

	m_rgbd_image->rawRgbRef() = Mat3b(m_calib_data->rawRgbSize());
	m_rgbd_image->rawDepthRef() = Mat1f(m_calib_data->raw_depth_size);
	m_rgbd_image->rawIntensityRef() = Mat1f(m_calib_data->rawRgbSize());

	m_rgbd_image->rawIntensityRef() = 0.f;
	m_rgbd_image->rawDepthRef() = 0.f;
	m_rgbd_image->rawRgbRef() = Vec3b(0,0,0);

	m_rgbd_image->rgbRef() = m_rgbd_image->rawRgbRef();
	m_rgbd_image->depthRef() = m_rgbd_image->rawDepthRef();
	m_rgbd_image->intensityRef() = m_rgbd_image->rawIntensityRef();

	m_rgbd_image->userLabelsRef() = cv::Mat1b(m_calib_data->raw_depth_size);
	m_rgbd_image->userLabelsRef() = 0u;

	//m_rgbd_image->setSkeletonData(new Skeleton());

	m_current_image->rawRgbRef() = Mat3b(m_calib_data->rawRgbSize());
	m_current_image->rawRgbRef() = Vec3b(0,0,0);
	m_current_image->rawDepthRef() = Mat1f(m_calib_data->raw_depth_size);
	m_current_image->rawDepthRef() = 0.f;
	m_current_image->rawIntensityRef() = Mat1f(m_calib_data->rawRgbSize());
	m_current_image->rawIntensityRef() = 0.f;

	m_current_image->rgbRef() = m_current_image->rawRgbRef();
	m_current_image->depthRef() = m_current_image->rawDepthRef();
	m_current_image->intensityRef() = m_current_image->rawIntensityRef();

	m_current_image->userLabelsRef() = cv::Mat1b(m_calib_data->raw_depth_size);
	m_current_image->userLabelsRef() = 0u;

	//m_current_image->setSkeletonData(new Skeleton());

	bool mapping_required = m_calib_data->rawRgbSize() != m_calib_data->raw_depth_size;
	if (!mapping_required)
	{
		m_rgbd_image->mappedRgbRef() = m_rgbd_image->rawRgbRef();
		m_rgbd_image->mappedDepthRef() = m_rgbd_image->rawDepthRef();
		m_current_image->mappedRgbRef() = m_current_image->rawRgbRef();
		m_current_image->mappedDepthRef() = m_current_image->rawDepthRef();
	}
	else
	{
		m_rgbd_image->mappedRgbRef() = Mat3b(m_calib_data->raw_depth_size);
		m_rgbd_image->mappedRgbRef() = Vec3b(0,0,0);
		m_rgbd_image->mappedDepthRef() = Mat1f(m_calib_data->rawRgbSize());
		m_rgbd_image->mappedDepthRef() = 0.f;
		m_current_image->mappedRgbRef() = Mat3b(m_calib_data->raw_depth_size);
		m_current_image->mappedRgbRef() = Vec3b(0,0,0);
		m_current_image->mappedDepthRef() = Mat1f(m_calib_data->rawRgbSize());
		m_current_image->mappedDepthRef() = 0.f;
	}

	

	ImageBayerGRBG bayer_decoder(ImageBayerGRBG::EdgeAware);
int cc = 0;
	while (!m_should_exit)
	{
		xn::SceneMetaData sceneMD;
	xn::DepthMetaData depthMD;
	xn::ImageMetaData rgbMD;

		//waitForNewEvent();
	boost::this_thread::interruption_point();
	::sleep(boost::posix_time::millisec(500));
	if(!(m_queue->CheckNeedToEnqueue()))
	{
		continue;
	}
	
		XnStatus status = m_ni_context.WaitAndUpdateAll();
	cout<<cc++<<endl;

if (status != XN_STATUS_OK)
	{
		//ntk_dbg(0) << "[ERROR] " << cv::format("%s failed: %s\n", what, xnGetStatusString(status));
		//ntk_throw_exception("Error in NiteRGBDGrabber.");
		//cout<<"XN_STATUS_NOT_OK"<<endl;
		continue;
	}
		//check_error(status, "WaitAndUpdateAll");

		//if (m_body_event_detector)
		//	m_body_event_detector->update();
		m_ni_depth_generator.GetMetaData(depthMD);
		m_ni_rgb_generator.GetMetaData(rgbMD);
		//sua them dk trackuser
		if(m_trackUser)
			m_ni_user_generator.GetUserPixels(0, sceneMD);

		const XnDepthPixel* pDepth = depthMD.Data();
		ntk_assert((depthMD.XRes() == m_current_image->rawDepth().cols)
			&& (depthMD.YRes() == m_current_image->rawDepth().rows),
			"Invalid image size.");

		// Convert to meters.
		float* raw_depth_ptr = m_current_image->rawDepthRef().ptr<float>();
		for (int i = 0; i < depthMD.XRes()*depthMD.YRes(); ++i)
			raw_depth_ptr[i] = pDepth[i]/1000.f;

		m_custom_bayer_decoding = true;
		if (m_custom_bayer_decoding)
		{
			uchar* raw_rgb_ptr = m_current_image->rawRgbRef().ptr<uchar>();
			bayer_decoder.fillRGB(rgbMD,
				m_current_image->rawRgb().cols, m_current_image->rawRgb().rows,
				raw_rgb_ptr);
			cvtColor(m_current_image->rawRgbRef(), m_current_image->rawRgbRef(), CV_RGB2BGR);
		}
		else
		{
			const XnUInt8* pImage = rgbMD.Data();
			ntk_assert(rgbMD.PixelFormat() == XN_PIXEL_FORMAT_RGB24, "Invalid RGB format.");
			uchar* raw_rgb_ptr = m_current_image->rawRgbRef().ptr<uchar>();
			for (int i = 0; i < rgbMD.XRes()*rgbMD.YRes()*3; i += 3)
				for (int k = 0; k < 3; ++k)
				{
					raw_rgb_ptr[i+k] = pImage[i+(2-k)];
				}
		}
		//if(m_trackUser)
		//{
		//	uchar* user_mask_ptr = m_current_image->userLabelsRef().ptr<uchar>();
		//	const XnLabel* pLabel = sceneMD.Data();
		//	for (int i = 0; i < sceneMD.XRes()*sceneMD.YRes(); ++i)
		//	{
		//		user_mask_ptr[i] = pLabel[i];
		//	}

		//	XnUserID user_ids[15];
		//	XnUInt16 num_users = 15;
		//	m_ni_user_generator.GetUsers(user_ids, num_users);

		//	// FIXME: only one user supported.
		//	for (int i = 0; i < num_users; ++i)
		//	{
		//		XnUserID user_id = user_ids[i];
		//		if (m_ni_user_generator.GetSkeletonCap().IsTracking(user_id))
		//		{
		//			m_current_image->skeletonRef()->computeJoints(user_id, m_ni_user_generator, m_ni_depth_generator);
		//			break;
		//		}
		//	}
		//}
		{
			//QWriteLocker locker(&m_lock);
			//m_current_image->swap(m_rgbd_image);
		}

		//advertiseNewFrame();

		//update va`o queue
		RGBDImage * m_last_image = new RGBDImage();
		m_current_image->copyTo(*m_last_image);
		m_queue->Enqueue(m_last_image);

		// Make sure we can be interrupted
			boost::this_thread::interruption_point();
	}
}