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
	rc.Run();

	////from kineck
	//RecontructorController rc;
	//rc.SetDestinationFolder("d:\\test");
	//rc.SetRecordedFolderData("grab1");
	//rc.SetLoadDataFromKineck(true);
	//rc.Run();

	return 0;
}
