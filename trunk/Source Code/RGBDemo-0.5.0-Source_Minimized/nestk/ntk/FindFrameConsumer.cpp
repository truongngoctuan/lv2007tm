
#include "FindFrameConsumer.h"

// The thread function reads data from the queue
void FindFrameConsumer::RunThread()
{
	//init sth before run
	if(this->IsSaveRawData() && this->IsSaveMappedData())
	{
		m_frame_recorder->setSaveOnlyRaw(false);
	}
	
	pose_estimator->m_use_icp = this->IsUseICP();
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
			//ref_points, img_points, 
			closest_view_index);

		if (pose_ok)
		{
			ilast_image = FindFrameConsumer::GetCurrentImageIndex();
			FindFrameConsumer::IncCurrentImageIndex();
		}
		//currentPose = pose_estimator->currentPose();
		//tc_pose_ok.stop();

		mtPoseEstimate.unlock();

		if (pose_ok)
		{
			//cap nhat currentFrame
			m_frame_recorder->setFrameIndex(ilast_image);
			std::string frame_dir = format("%s/view%04d", 
				this->GetRecordedFolderData().c_str(), 
				ilast_image);

			string NewFile = format("%s\\color%04d.png", this->GetDestinationFolder().c_str(),ilast_image);
			//save frame
			if (this->IsSaveRawData() && m_frame_recorder)
			{
				TimeCountThread tc_saveCurrentFrame(m_id, "saveCurrentFrame", 2);
				m_frame_recorder->saveCurrentFrame(*m_last_image);
				//rename((frame_dir + "/raw/color.png").c_str(), NewFile.c_str());
				tc_saveCurrentFrame.stop();
			}

			//----------------------------------------------------------------
			//save pairs 3d
			if(this->hasFilterFlag(FindFrameConsumer::Flags::Notprocess) && this->IsSavePairs())
			{
				pose_estimator->CalulatePairs(false, ref_points, img_points);
				this->SavePairs(closest_view_index, format("%s\\NotprocessPairs_%04d_%04d.txt", this->GetDestinationFolder().c_str(), closest_view_index, ilast_image),
									  ref_points, img_points);
			}
			if(this->hasFilterFlag(FindFrameConsumer::Flags::NotDecreaseSameVertex) && this->IsSavePairs())
			{
				pose_estimator->CalulatePairs(true, ref_points, img_points);
				this->SavePairs(closest_view_index, format("%s\\NotDecreaseSameVertexPairs_%04d_%04d.txt", this->GetDestinationFolder().c_str(), closest_view_index, ilast_image),
									  ref_points, img_points);
			}

			//----------------------------------------------------------------
			//save ply
			if(this->hasFilterFlag(FindFrameConsumer::Flags::Notprocess))
			{
				SurfelsRGBDModeler modeler;
				modeler.setMinViewsPerSurfel(1);
				SaveFilePly(modeler, m_last_image, ilast_image, *(m_last_image->calibration()->depth_pose), 
					format("%s\\Notprocess_%04d.ply", this->GetDestinationFolder().c_str(), ilast_image),
					format("%s\\Notprocess_%04d.ply", this->GetDestinationFolderTemp().c_str(), ilast_image));
			}

			if(this->hasFilterFlag(FindFrameConsumer::Flags::NotDecreaseSameVertex))
			{
				SurfelsRGBDModeler modeler;
				modeler.setMinViewsPerSurfel(1);
				SaveFilePly(modeler, m_last_image, ilast_image, currentPose, 
					format("%s\\NotDecreaseSameVertex_%04d.ply", this->GetDestinationFolder().c_str(), ilast_image),
					format("%s\\NotDecreaseSameVertex_%04d.ply", this->GetDestinationFolderTemp().c_str(), ilast_image));

				m_vtFileNameNotDecrease.push_back(format("%s\\NotDecreaseSameVertex_%04d.ply", this->GetDestinationFolder().c_str(), ilast_image));
			}

			if(true)
			{
				SurfelsRGBDModeler modeler;
				modeler.setMinViewsPerSurfel(1);
				pose_estimator->m_image_data;
				for (int i = 0; i < pose_estimator->m_image_data.size(); i++)
				{
					modeler.addNewView2(*(m_last_image->calibration()),
						pose_estimator->m_image_data[i].depth, 
						pose_estimator->m_image_data[i].color, 
						pose_estimator->m_image_data[i].depth_pose);
				}
				modeler.computeMesh();
				modeler.currentMesh().saveToPlyFile(format("%s\\All_%04d.ply", this->GetDestinationFolderTemp().c_str(), ilast_image).c_str());
				rename(format("%s\\All_%04d.ply", this->GetDestinationFolderTemp().c_str(), ilast_image).c_str(), format("%s\\All_%04d.ply", this->GetDestinationFolder().c_str(), ilast_image).c_str());
			}

			if(this->hasFilterFlag(FindFrameConsumer::Flags::DecreaseSameVertex))
			{
				mtmodeler.lock();
				SaveFilePly(current_modeler, m_last_image, ilast_image, currentPose, 
					format("%s\\DecreaseSameVertex_%04d.ply", this->GetDestinationFolder().c_str(), ilast_image),
					format("%s\\DecreaseSameVertex_%04d.ply", this->GetDestinationFolderTemp().c_str(), ilast_image));
				mtmodeler.unlock();
			}
		}

		delete m_last_image;

		//SaveFileTotalNotDecreaseSameVertex("d:\\listply.txt");

		// Make sure we can be interrupted
		boost::this_thread::interruption_point();
	}
}

void FindFrameConsumer::SaveFilePly(SurfelsRGBDModeler& modeler,
									RGBDImage * m_last_image, int ilast_image, Pose3D currentPose,
									string strFileName, string strTempFileName)
{
	//relative pose là so với frame đầu tiên 
	//chứ ko phải so với frame trước đó
	TimeCountThread tc_addNewView(m_id, "addNewView", 2);
	modeler.addNewView(*m_last_image, currentPose);
	tc_addNewView.stop();

	TimeCountThread tc_computeMesh(m_id, "computeMesh", 2);
	//current_modeler.computeMesh();
	modeler.computeNewFrameMesh();
	tc_computeMesh.stop();

	TimeCountThread tc_saveToPlyFile(m_id, "saveToPlyFile", 2);
	modeler.currentMesh().saveToPlyFile(strTempFileName.c_str());
	//current_modeler.currentMesh().saveNewFrameToPlyFile(strDestinationFileName.c_str());
	rename(strTempFileName.c_str(), strFileName.c_str());
	tc_saveToPlyFile.stop();
	
}

void FindFrameConsumer::SavePairs(int closest_view_index, string strFileName,
								  std::vector<cv::Point3f> ref_points, std::vector<cv::Point3f> img_points)
{
	//save pairs 3d
	if (closest_view_index != -1)
	{
		std::ofstream ofs (strFileName.c_str());
		ofs<<ref_points.size()<<endl;
		for (int i = 0; i < ref_points.size(); i++)
		{
			ofs << ref_points[i].x * 1000.0f<<" "<<ref_points[i].y * 1000.0f<<" "<<ref_points[i].z * 1000.0f<< " ";
			ofs << img_points[i].x * 1000.0f<<" "<<img_points[i].y * 1000.0f<<" "<<img_points[i].z * 1000.0f<<endl;
		}
		ofs.close();
	}
}

void FindFrameConsumer::SaveFileTotalNotDecreaseSameVertex(string strName)
{
	ofstream ofs((strName).c_str());
	ofs<<m_vtFileNameNotDecrease.size()<<endl;
	for (int i = 0; i < m_vtFileNameNotDecrease.size(); i++)
	{
		ofs<<m_vtFileNameNotDecrease[i]<<endl;
	}
}