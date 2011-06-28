
#include "FindFrameConsumer.h"

// The thread function reads data from the queue
void FindFrameConsumer::operator () ()
{
	//init sth before run
	if(this->IsSaveRawData() && this->IsSaveMappedData())
	{
		m_frame_recorder->setSaveOnlyRaw(false);
	}

	int ilast_image;
	Pose3D currentPose;
	bool pose_ok;
	while (true)
	{
		//m_mutex.lock();

		RGBDImage * m_last_image = m_queue->Dequeue(ilast_image);
		//m_mutex.unlock();

		std::vector<cv::Point3f> ref_points;
		std::vector<cv::Point3f> img_points;
		int closest_view_index = -1;

		TimeCountThread tc_rgbd_process(m_id, "processImage", 2);
		m_processor->processImage(*m_last_image);
		tc_rgbd_process.stop();

		pose_ok = false;
		//mtPoseEstimate.lock();
		TimeCountThread tc_pose_ok(m_id, "pose_ok", 2);
		pose_ok = pose_estimator->estimateNewPose(*m_last_image, currentPose,
			ref_points, img_points, closest_view_index);

		if (pose_ok)
		{
			FindFrameConsumer::IncCurrentImageIndex();
			ilast_image = FindFrameConsumer::GetCurrentImageIndex();
		}
		//currentPose = pose_estimator->currentPose();
		//tc_pose_ok.stop();

		mtPoseEstimate.unlock();

		if (pose_ok)
		{
			//cap nhat currentFrame
			m_frame_recorder->setFrameIndex(ilast_image);
			std::string frame_dir = format("%s/view%04d", 
				m_frame_recorder->directory().c_str(), 
				ilast_image);

			string NewFile = format("d:\\test\\color%04d.png", ilast_image);
			//save
			if (this->IsSaveRawData() && m_frame_recorder)
			{
				TimeCountThread tc_saveCurrentFrame(m_id, "saveCurrentFrame", 2);
				m_frame_recorder->saveCurrentFrame(*m_last_image);
				//rename((frame_dir + "/raw/color.png").c_str(), NewFile.c_str());
				tc_saveCurrentFrame.stop();
			}

			//{//tao file ply,...
			mtmodeler.lock();
			SurfelsRGBDModeler current_modeler;
			current_modeler.setMinViewsPerSurfel(1);

			//relative pose là so với frame đầu tiên 
			//chứ ko phải so với frame trước đó
			TimeCountThread tc_addNewView(m_id, "addNewView", 2);
			current_modeler.addNewView(*m_last_image, currentPose);
			tc_addNewView.stop();

			TimeCountThread tc_computeMesh(m_id, "computeMesh", 2);
			//current_modeler.computeMesh();
			current_modeler.computeNewFrameMesh();
			tc_computeMesh.stop();

			TimeCountThread tc_saveToPlyFile(m_id, "saveToPlyFile", 2);
			string strDestinationFileName = format("d:\\scene_mesh_%04d.ply", ilast_image);
			current_modeler.currentMesh().saveToPlyFile(strDestinationFileName.c_str());
			//current_modeler.currentMesh().saveNewFrameToPlyFile(strDestinationFileName.c_str());
			rename((strDestinationFileName).c_str(), format("d:\\test\\scene_mesh_%04d.ply", ilast_image).c_str());
			tc_saveToPlyFile.stop();
			mtmodeler.unlock();

			//save pairs 3d
			if (closest_view_index != -1)
			{
				std::ofstream ofs (format("d:\\test\\pairs_%04d_%04d.txt", closest_view_index, ilast_image).c_str());
				ofs<<ref_points.size()<<endl;
				for (int i = 0; i < ref_points.size(); i++)
				{
					ofs << ref_points[i].x * 1000.0f<<" "<<ref_points[i].y * 1000.0f<<" "<<ref_points[i].z * 1000.0f<< " ";
					ofs << img_points[i].x * 1000.0f<<" "<<img_points[i].y * 1000.0f<<" "<<img_points[i].z * 1000.0f<<endl;
				}
				ofs.close();
			}
		}

		delete m_last_image;

		// Make sure we can be interrupted
		boost::this_thread::interruption_point();
	}
}