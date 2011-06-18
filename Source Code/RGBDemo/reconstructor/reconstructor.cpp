/**
 * This file is part of the rgbdemo project.
 *
 * This program is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
 * Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with this program.  If not, see <http://www.gnu.org/licenses/>.
 *
 * Author: Nicolas Burrus <nicolas@burrus.name>, (C) 2010, 2011
 */

#include <ntk/ntk.h>
#include <ntk/camera/calibration.h>
#ifdef NESTK_USE_OPENNI
# include <ntk/camera/nite_rgbd_grabber.h>
#endif

#include <iostream>
#include <stdio.h>
#include <stdlib.h>
#include <cstdlib>
#include <sstream>
#include <iomanip>

#include <ntk/image/sift_gpu.h>
#include <ntk/camera/opencv_grabber.h>
#include <ntk/camera/file_grabber.h>
#include <ntk/camera/rgbd_frame_recorder.h>

#ifdef NESTK_USE_FREENECT
# include <ntk/camera/kinect_grabber.h>
#endif

#include <ntk/mesh/mesh_generator.h>
#include <ntk/mesh/surfels_rgbd_modeler.h>
#include "GuiController.h"
#include "ModelAcquisitionController.h"

#include <QApplication>
#include <QMetaType>

//moi them vao
#include <ntk/numeric/levenberg_marquart_minimizer.h>
#include "file_grabber2.h"

using namespace ntk;
using namespace cv;

namespace opt
{
  ntk::arg<const char*> dir_prefix("--prefix", "Directory prefix for output", "grab1");
  ntk::arg<const char*> calibration_file("--calibration", "Calibration file (yml)", 0);
  ntk::arg<const char*> image("--image", "Fake mode, use given still image", 0);
  ntk::arg<const char*> directory("--directory", "Fake mode, use all view???? images in dir.", 0);
  ntk::arg<int> camera_id("--camera-id", "Camera id for opencv", 0);
  ntk::arg<bool> sync("--sync", "Synchronization mode", 0);
  ntk::arg<bool> freenect("--freenect", "Force freenect driver", 0);
  ntk::arg<bool> high_resolution("--highres", "High resolution color image.", 0);
  ntk::arg<bool> use_icp("--icp", "Use ICP to refine pose estimation", 0);
}

string str_itoa(int i, int digit)
{
	char c[20];
	itoa(i, c, 10);
	string strTemp = string(c);
	while (strTemp.length() < digit)
	{
		strTemp = "0" + strTemp;
	}
	return strTemp;
}

void asd ()
{
	
	//lam sao doc tu file_grabber
	//	doc tu thu muc
	//	chuyen raw img thanh mapped
	//	prrocess img
	//lam sao de co calibration
	//lam sao truyen file vao no tra ra ket qua(relative pose, file .ply)
	//	tinh new pose
	//	tinh ... cho tung cloud
	//	xuat ra file

	opt::directory() ="grab1";
	file_grabber2* grabber2 = 0;
	std::string path = opt::directory();
	grabber2 = new file_grabber2(path);

	opt::calibration_file() = "kineck_calibration.yml";
	ntk::RGBDCalibration* calib_data = 0;
	if (opt::calibration_file())
	{
		calib_data = new RGBDCalibration();
		calib_data->loadFromFile(opt::calibration_file());
	}
	//ntk_ensure(calib_data, "You must specify a calibration file (--calibration)");
	grabber2->setCalibrationData(*calib_data);

	ntk::RGBDImage m_last_image;
	ntk::RGBDProcessor* m_processor;
	m_processor = new ntk::NiteProcessor();
	m_processor->setFilterFlag(RGBDProcessor::ComputeNormals, 1);
	m_processor->setMaxNormalAngle(90);
	m_processor->setFilterFlag(RGBDProcessor::ComputeMapping, true);

	RelativePoseEstimator* pose_estimator = 0;
	//FeatureSetParams params ("FAST", "BRIEF64", true);
	FeatureSetParams params ("SURF", "SURF64", true);
	pose_estimator = new RelativePoseEstimatorFromImage(params, opt::use_icp());

	SurfelsRGBDModeler modeler;
	modeler.setMinViewsPerSurfel(1);

	while (true)
	{
		if (grabber2->GetNextImage())
		{
			//do sth
			cout<<grabber2->m_current_image_index<<endl;

			//raw -->mapped img
			grabber2->copyImageTo(m_last_image);
			TimeCount tc_rgbd_process("m_processor.processImage", 2);
			m_processor->processImage(m_last_image);
			tc_rgbd_process.stop();

			bool pose_ok = pose_estimator->estimateNewPose(m_last_image);
			if (pose_ok)
			{//tao file ply,...
				modeler.addNewView(m_last_image, pose_estimator->currentPose());
				modeler.computeMesh();

				//m_controller.modelAcquisitionWindow()->ui->mesh_view->addMesh(m_modeler.currentMesh(), Pose3D(), MeshViewer::FLAT);

				//save
				string strDestinationFileName = "scene_mesh_" + str_itoa(grabber2->m_current_image_index, 4)  + ".ply";
				modeler.computeSurfaceMesh();
				modeler.currentMesh().saveToPlyFile(strDestinationFileName.c_str());
			}
		}
		else
		{
			break;
		}
	}
}

int main (int argc, char** argv)
{
	asd ();

	return 0;

	//--------------------------------------------------

  arg_base::set_help_option("-h");
  arg_parse(argc, argv);
  ntk_debug_level = 1;
  cv::setBreakOnError(true);

  QApplication::setGraphicsSystem("raster");
  QApplication app (argc, argv);

  const char* fake_dir = opt::image();
  //bool is_directory = true;
  //opt::directory() ="grab2";

  bool is_directory = opt::directory() != 0;
  if (opt::directory())
    fake_dir = opt::directory();

  ntk::RGBDProcessor* processor = 0;
  RGBDGrabber* grabber = 0;

  bool use_openni = !opt::freenect();
#ifndef NESTK_USE_OPENNI
  use_openni = false;
#endif

  if (opt::image() || opt::directory())
  {
    std::string path = opt::image() ? opt::image() : opt::directory();
    FileGrabber* file_grabber = new FileGrabber(path, opt::directory() != 0);
    grabber = file_grabber;
  }
#ifdef NESTK_USE_OPENNI
  else if (use_openni)
  {
    // Config dir is supposed to be next to the binaries.
    QDir prev = QDir::current();
    QDir::setCurrent(QApplication::applicationDirPath());
    NiteRGBDGrabber* k_grabber = new NiteRGBDGrabber();
    if (opt::high_resolution())
      k_grabber->setHighRgbResolution(true);
    k_grabber->initialize();
    QDir::setCurrent(prev.absolutePath());
    grabber = k_grabber;
  }
#endif
#ifdef NESTK_USE_FREENECT
  else
  {
    KinectGrabber* k_grabber = new KinectGrabber();
    k_grabber->initialize();
    k_grabber->setIRMode(false);
    grabber = k_grabber;
  }
#endif

  ntk_ensure(grabber, "Could not create any grabber. Kinect support built?");

  if (use_openni)
  {
    processor = new ntk::NiteProcessor();
  }
  else
  {
    processor = new ntk::KinectProcessor();
  }

  if (opt::sync())
    grabber->setSynchronous(true);

  RGBDFrameRecorder frame_recorder (opt::dir_prefix());
  frame_recorder.setSaveOnlyRaw(false);

  ntk::RGBDCalibration* calib_data = 0;
  if (opt::calibration_file())
  {
    calib_data = new RGBDCalibration();
    calib_data->loadFromFile(opt::calibration_file());
  }
  else if (use_openni)
  {
    calib_data = grabber->calibrationData();
	//  calib_data = estimateCalibration();
  }
  else if (QDir::current().exists("kinect_calibration.yml"))
  {
    {
      ntk_dbg(0) << "[WARNING] Using kinect_calibration.yml in current directory";
      ntk_dbg(0) << "[WARNING] use --calibration to specify a different file.";
    }
    calib_data = new RGBDCalibration();
    calib_data->loadFromFile("kinect_calibration.yml");
  }

  ntk_ensure(calib_data, "You must specify a calibration file (--calibration)");
  grabber->setCalibrationData(*calib_data);
  calib_data->saveToFile("kineck_calibration.yml");

  GuiController gui_controller (*grabber, *processor);
  grabber->addEventListener(&gui_controller);
  gui_controller.setFrameRecorder(frame_recorder);

  if (opt::sync())
    gui_controller.setPaused(true);

  SurfelsRGBDModeler modeler;
  modeler.setMinViewsPerSurfel(1);
  processor->setFilterFlag(RGBDProcessor::ComputeNormals, 1);
  processor->setMaxNormalAngle(90);
  processor->setFilterFlag(RGBDProcessor::ComputeMapping, true);

  ModelAcquisitionController* acq_controller = 0;
  acq_controller = new ModelAcquisitionController (gui_controller, modeler);

  RelativePoseEstimator* pose_estimator = 0;
  //FeatureSetParams params ("FAST", "BRIEF64", true);
  FeatureSetParams params ("SURF", "SURF64", true);
  pose_estimator = new RelativePoseEstimatorFromImage(params, opt::use_icp());

  acq_controller->setPoseEstimator(pose_estimator);
  gui_controller.setModelAcquisitionController(*acq_controller);

  grabber->start();

  app.exec();
  delete acq_controller;
}
