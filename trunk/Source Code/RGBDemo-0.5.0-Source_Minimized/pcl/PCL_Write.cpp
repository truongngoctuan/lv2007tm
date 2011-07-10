#include "PCL_Write.h"
#include <iostream>
#include <pcl/io/pcd_io.h>
#include <pcl/point_types.h>

PCL_Write::PCL_Write(void)
{
}


PCL_Write::~PCL_Write(void)
{
}

bool PCL_Write::Auto(const char *strPCDFile)
{
	pcl::PointCloud<pcl::PointXYZ> cloud;

  // Fill in the cloud data
  cloud.width    = 5;
  cloud.height   = 1;
  cloud.is_dense = false;
  cloud.points.resize (cloud.width * cloud.height);

  for (size_t i = 0; i < cloud.points.size (); ++i)
  {
    cloud.points[i].x = 1024 * rand () / (RAND_MAX + 1.0);
    cloud.points[i].y = 1024 * rand () / (RAND_MAX + 1.0);
    cloud.points[i].z = 1024 * rand () / (RAND_MAX + 1.0);
  }

  pcl::io::savePCDFileASCII (strPCDFile, cloud);
  std::cerr << "Saved " << cloud.points.size () << " data points to test_pcd.pcd." << std::endl;

  for (size_t i = 0; i < cloud.points.size (); ++i)
    std::cerr << "    " << cloud.points[i].x << " " << cloud.points[i].y << " " << cloud.points[i].z << std::endl;

	return true;
}