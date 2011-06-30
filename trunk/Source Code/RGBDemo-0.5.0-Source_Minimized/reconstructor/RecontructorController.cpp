#include "RecontructorController.h"
using namespace boost::filesystem3;

RecontructorController::RecontructorController(void)
{
	m_iSavePlyMode = 0;
	//SetSaveFilePlyMode(RecontructorController::Flags::DecreaseSameVertex, true);
	m_strCommandFile = "cm.txt";
}

RecontructorController::~RecontructorController(void)
{
}

void RecontructorController::Run()
{
	if (m_bIsFromKineck)
	{
		boost::filesystem3::remove_all(path(m_strDestinationFolder));
		boost::filesystem3::remove_all(path(m_strRecordedFolderData));

		filesystem3::create_directory(path(m_strDestinationFolder));
		filesystem3::create_directory(path(m_strDestinationFolderTemp));

		filesystem3::create_directory(path(m_strRecordedFolderData));

		RunFromKineck();
	}
	else
	{
		boost::filesystem3::remove_all(path(m_strDestinationFolder));

		filesystem3::create_directory(path(m_strDestinationFolder));
		filesystem3::create_directory(path(m_strDestinationFolderTemp));

		RunFromRecordedData();
	}
	
}

void RecontructorController::RunFromKineck()
{
	ntk_debug_level = 1;
	// Display the number of processors/cores
	cout<<boost::thread::hardware_concurrency()
		<<" processors/cores detected."<<endl<<endl;
	cout<<"When threads are running, press enter to stop"<<endl;

	// The number of producers/consumers
	int nrProducers, nrConsumers;

	// The shared queue
	SynchronisedQueue<RGBDImage *> queue;
	queue.SetMaxQueueElement(1);

	nrProducers = 1;

	nrConsumers = 1;
	FindFrameConsumer::Init();

	// Create producers
	boost::thread_group producers;
	FileGrabberProducer p(0, &queue);
	p.initialize();
	producers.create_thread(p);

	// Create consumers
	boost::thread_group consumers;
	FindFrameConsumer* c = new FindFrameConsumer(0, &queue, m_strRecordedFolderData.c_str(), 0);
	c->SetSaveRawData(m_bIsSaveRawData);
	c->SetSaveMappedData(m_bIsSaveMappedData);

	c->SetDestinationFolder(m_strDestinationFolder);
	c->SetDestinationFolderTemp(m_strDestinationFolderTemp);
	c->SetRecordedFolderData(m_strRecordedFolderData);
	c->SetPathCalibrationData(m_strPathCalibrationData);

	c->setFilterFlags(m_iSavePlyMode);
	c->SetSavePairs(m_bSavePairs);

	c->SetUseICP(m_bUseICP);
	boost::thread thc(thread_adapter (&FindFrameConsumer::do_thread, c));
	consumers.add_thread(&thc);
	//consumers.create_thread(c);

	//FIX ME: change this to sth like check signal end this thread
	// Wait for enter (two times because the return from the 
	// previous cin is still in the buffer)
	//getchar(); getchar();

	while (true)
	{
		if (boost::filesystem3::exists(path(m_strDestinationFolder + "\\" + m_strCommandFile)))
		{
			ifstream ifs((m_strDestinationFolder + "\\" + m_strCommandFile).c_str());
			string strcm;
			ifs >>strcm;
			ifs.close();
			if (strcm == "exit")
			{
				filesystem3::remove(path(m_strDestinationFolder + "\\" + m_strCommandFile));
				break;
			}
		}
		else
		{
			::sleep(boost::posix_time::millisec(500));
		}
	}

	// Interrupt the threads and stop them

	producers.interrupt_all(); producers.join_all();
	consumers.interrupt_all(); consumers.join_all();
	consumers.remove_thread(&thc);
	c->SaveFileTotalNotDecreaseSameVertex(m_strDestinationFolder + "\\listply.txt");

	MyAlign::Auto(m_strDestinationFolder + "\\listply.txt", m_strDestinationFolder);
}

void RecontructorController::RunFromRecordedData()
{
	ntk_debug_level = 1;
	// Display the number of processors/cores
	cout<<boost::thread::hardware_concurrency()
		<<" processors/cores detected."<<endl<<endl;
	cout<<"When threads are running, press enter to stop"<<endl;

	// The number of producers/consumers
	int nrProducers, nrConsumers;

	// The shared queue
	SynchronisedQueue<RGBDImage *> queue;
	queue.SetMaxQueueElement(1);

	nrProducers = 1;
	
	nrConsumers = 1;
	FindFrameConsumer::Init();
	// Create producers
	boost::thread_group producers;
	
	ModeRecordGrabberProducer p(0, &queue, m_strRecordedFolderData);
	ntk::RGBDCalibration* calib_data = new RGBDCalibration();
	calib_data->loadFromFile(m_strPathCalibrationData.c_str());
	p.setCalibration(calib_data);
	producers.create_thread(p);

	// Create consumers
	boost::thread_group consumers;
	FindFrameConsumer* c = new FindFrameConsumer(0, &queue, m_strRecordedFolderData.c_str(), 0);
	c->SetSaveRawData(m_bIsSaveRawData);
	c->SetSaveMappedData(m_bIsSaveMappedData);

	c->SetDestinationFolder(m_strDestinationFolder);
	c->SetDestinationFolderTemp(m_strDestinationFolderTemp);

	c->SetRecordedFolderData(m_strRecordedFolderData);
	c->SetPathCalibrationData(m_strPathCalibrationData);
	c->setFilterFlags(m_iSavePlyMode);
	c->SetSavePairs(m_bSavePairs);
	c->SetUseICP(m_bUseICP);
	boost::thread thc(thread_adapter (&FindFrameConsumer::do_thread, c));
	consumers.add_thread(&thc);
	//consumers.create_thread(c);

	//FIX ME: change this to sth like check signal end this thread
	// Wait for enter (two times because the return from the 
	// previous cin is still in the buffer)
	//getchar(); getchar();

	while (true)
	{
		if (boost::filesystem3::exists(path(m_strDestinationFolder + "\\" + m_strCommandFile)))
		{
			ifstream ifs((m_strDestinationFolder + "\\" + m_strCommandFile).c_str());
			string strcm;
			ifs >>strcm;
			ifs.close();
			if (strcm == "exit")
			{
				filesystem3::remove(path(m_strDestinationFolder + "\\" + m_strCommandFile));
				break;
			}
		}
		else
		{
			::sleep(boost::posix_time::millisec(500));
		}
	}

	// Interrupt the threads and stop them

	producers.interrupt_all(); producers.join_all();
	consumers.interrupt_all(); consumers.join_all();
	consumers.remove_thread(&thc);
	c->SaveFileTotalNotDecreaseSameVertex(m_strDestinationFolder + "\\listply.txt");

	MyAlign::Auto(m_strDestinationFolder + "\\listply.txt", m_strDestinationFolder);
}