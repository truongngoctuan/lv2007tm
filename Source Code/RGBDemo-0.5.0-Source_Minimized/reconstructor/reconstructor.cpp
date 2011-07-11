#pragma once
#include "RecontructorController.h"
#include "MyAlign.h"
//#include "PCL_Write.h"
#include <string>
using namespace std;

int main (int argc, char* argv[])
{
	//PCL_Write::Auto("pcd.pcd");
	string strMode = argv[1];
	if (strMode == "player")
	{
		if (argc == 5)
		{
			string strDestinationFolder = argv[2];
			string strRecordedFolderData = argv[3];
			string strPathCalibrationData = argv[4];

			//fromrecord
			RecontructorController rc;
			rc.SetDestinationFolder(strDestinationFolder);
			rc.SetRecordedFolderData(strRecordedFolderData);
			rc.SetPathCalibrationData(strPathCalibrationData);
			rc.SetLoadDataFromKineck(false);
			//rc.SetSaveFilePlyMode(RecontructorController::Flags::Notprocess, true);
			rc.SetSaveFilePlyMode(RecontructorController::Flags::NotDecreaseSameVertex, true);
			//rc.SetSaveFilePlyMode(RecontructorController::Flags::SaveFinalPly, true);
			//rc.SetSaveFilePlyMode(RecontructorController::Flags::DecreaseSameVertex, true);
			rc.SetSavePairs(false);
			rc.SetUseICP(true);
			rc.Run();
		}
	}

	if ( strMode == "kineck")
	{
		if (argc == 5)
		{
			string strDestinationFolder = argv[2];
			string strRecordedFolderData = argv[3];

			RecontructorController rc;
			rc.SetDestinationFolder(strDestinationFolder);
			rc.SetRecordedFolderData(strRecordedFolderData);
			//rc.SetPathCalibrationData("kineck_calibration.yml");
			rc.SetLoadDataFromKineck(true);
			//rc.SetSaveFilePlyMode(RecontructorController::Flags::Notprocess, true);
			rc.SetSaveFilePlyMode(RecontructorController::Flags::NotDecreaseSameVertex, true);
			rc.SetSaveFilePlyMode(RecontructorController::Flags::DecreaseSameVertex, true);
			//rc.SetSaveFilePlyMode(RecontructorController::Flags::SaveFinalPly, true);
			rc.SetSavePairs(false);
			rc.SetUseICP(true);
			rc.Run();
		}
	}

	return 0;
}
