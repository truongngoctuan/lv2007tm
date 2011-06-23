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
//#define NESTK_USE_PCL

#include <ntk/ntk.h>
#include <ntk/camera/calibration.h>
//#ifdef NESTK_USE_OPENNI
//# include <ntk/camera/nite_rgbd_grabber.h>
//#endif

#include <iostream>
#include <stdio.h>
#include <stdlib.h>
#include <cstdlib>
#include <sstream>
#include <iomanip>

#include <ntk/image/sift_gpu.h>
//#include <ntk/camera/opencv_grabber.h>
//#include <ntk/camera/file_grabber.h>
#include <ntk/camera/rgbd_frame_recorder.h>

#include <ntk/mesh/mesh_generator.h>
#include <ntk/mesh/surfels_rgbd_modeler.h>
#include <ntk/numeric/levenberg_marquart_minimizer.h>
#include <boost/thread.hpp>
#include <string>
#include <sstream>
#include <ntk/SynchronisedQueue.h>
#include <ntk/FileGrabberProducer.h>
#include <ntk/FindFrameConsumer.h>

using namespace std;
using namespace boost;
using namespace boost::this_thread;
using namespace ntk;
using namespace cv;

namespace opt
{
	ntk::arg<const char*> dir_prefix("--prefix", "Directory prefix for output", "grab1");
	ntk::arg<int> first_index("--istart", "First image index", 0);
}

//how to use thread in boost library
//http://www.quantnet.com/cplusplus-multithreading-boost/
//http://en.highscore.de/cpp/boost/

//how to fix error when linking to thread boost library
//https://svn.boost.org/trac/boost/ticket/2226
namespace boost {
	struct thread::dummy {};
}

int main (int argc, char** argv)
{
	arg_base::set_help_option("-h");
	arg_parse(argc, argv);
	ntk_debug_level = 1;
	cv::setBreakOnError(true);

	// Display the number of processors/cores
	cout<<boost::thread::hardware_concurrency()
		<<" processors/cores detected."<<endl<<endl;
	cout<<"When threads are running, press enter to stop"<<endl;

	// The number of producers/consumers
	int nrProducers, nrConsumers;

	// The shared queue
	SynchronisedQueue<RGBDImage *> queue;

	// Ask the number of producers
	cout<<"How many producers do you want? : ";
	//cin>>nrProducers;
	nrProducers = 1;
	cout<<1<<endl;

	// Ask the number of consumers
	cout<<"How many consumers do you want? : ";
	cin>>nrConsumers;

	queue.SetMaxQueueElement(1);
	FindFrameConsumer::Init();

	// Create producers
	boost::thread_group producers;
	FileGrabberProducer p(0, &queue);
	p.initialize();
	producers.create_thread(p);

	// Create consumers
	boost::thread_group consumers;
	for (int i=0; i<nrConsumers; i++)
	{
		FindFrameConsumer c(i, &queue, opt::dir_prefix(), opt::first_index());
		consumers.create_thread(c);
	}
	// Wait for enter (two times because the return from the 
	// previous cin is still in the buffer)
	getchar(); getchar();

	// Interrupt the threads and stop them
	producers.interrupt_all(); producers.join_all();
	consumers.interrupt_all(); consumers.join_all();

	return 0;
}
