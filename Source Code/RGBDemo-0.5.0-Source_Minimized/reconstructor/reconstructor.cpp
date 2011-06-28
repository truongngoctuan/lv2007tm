#pragma once
#include "RecontructorController.h"
int main (int argc, char** argv)
{
	//fromrecord
	RecontructorController rc;
	rc.SetDestinationFolder("d:\\test");
	rc.SetRecordedFolderData("grab1");
	rc.SetPathCalibrationData("kineck_calibration.yml");
	rc.SetLoadDataFromKineck(false);
	rc.SetSaveFilePlyMode(RecontructorController::Flags::Notprocess, true);
	rc.SetSaveFilePlyMode(RecontructorController::Flags::NotDecreaseSameVertex, true);
	rc.SetSavePairs(true);
	rc.SetUseICP(true);
	rc.Run();

	//RecontructorController rc;
	//rc.SetDestinationFolder("d:\\test");
	//rc.SetRecordedFolderData("grab1");
	//rc.SetPathCalibrationData("kineck_calibration.yml");
	//rc.SetLoadDataFromKineck(true);
	////rc.SetSaveFilePlyMode(RecontructorController::Flags::Notprocess, true);
	//rc.SetSaveFilePlyMode(RecontructorController::Flags::NotDecreaseSameVertex, true);
	//rc.SetSaveFilePlyMode(RecontructorController::Flags::DecreaseSameVertex, true);
	//rc.SetSavePairs(true);
	//rc.SetUseICP(true);
	//rc.Run();
	return 0;
}
