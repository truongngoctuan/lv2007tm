#pragma once

#include <QDir>
#include <QStringList>
#include <ntk/ntk.h>
using namespace ntk;

class file_grabber2
{
public:
	file_grabber2(void);
	~file_grabber2(void);

	  file_grabber2(const std::string& path);
public:
	bool GetNextImage();
	int m_current_image_index;
private:
  QDir m_path;
  QStringList m_image_list;
  RGBDImage m_buffer_image;
  
  //bool m_is_directory;
  ntk::RGBDCalibration* m_calib_data;

    /*! Set the calibration data that will be included in each image. */
public:
  void setCalibrationData(ntk::RGBDCalibration& data)
  { m_calib_data = &data; }

  ntk::RGBDCalibration* calibrationData()
  { return m_calib_data; }

  const ntk::RGBDCalibration* calibrationData() const
  { return m_calib_data; }

  /*! Thread safe deep copy. */
  void copyImageTo(RGBDImage& image);
};
