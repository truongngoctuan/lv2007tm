/**
 * This file is part of the nestk library.
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
 * Author: Nicolas Burrus <nicolas.burrus@uc3m.es>, (C) 2010
 */

#include "rgbd_frame_recorder.h"

#include <ntk/ntk.h>

using namespace cv;

namespace ntk
{

  RGBDFrameRecorder :: RGBDFrameRecorder(const std::string& directory)
    : m_frame_index(0), m_only_raw(true), m_use_binary_raw(false)
  {
    setDirectory(directory);
  }

  void RGBDFrameRecorder :: setDirectory(const std::string& directory)
  {
    m_dir = directory;
    m_frame_index = 0;
	boost::filesystem::path p(m_dir); 
    boost::filesystem::create_directory(p);
  }

  void RGBDFrameRecorder :: setUseBinaryRaw(bool use_it)
  {
      m_use_binary_raw = use_it;
  }

  void RGBDFrameRecorder :: saveCurrentFrame(const RGBDImage& image)
  {
    std::string frame_dir = format("%s/view%04d", m_dir.c_str(), m_frame_index);
    std::string raw_frame_dir = format("%s/raw", frame_dir.c_str(), m_frame_index);

	boost::filesystem::path p(frame_dir); 
    boost::filesystem::create_directory(p);

	boost::filesystem::path p2(raw_frame_dir); 
    boost::filesystem::create_directory(p2);

    std::string filename;

    if (!m_only_raw)
    {
      filename = cv::format("%s/color.png", frame_dir.c_str());
      imwrite(filename, image.rgb());
    }

    filename = cv::format("%s/raw/color.png", frame_dir.c_str());
    imwrite(filename, image.rawRgb());

    if (!m_only_raw && image.mappedDepth().data)
    {
      filename = cv::format("%s/mapped_depth.png", frame_dir.c_str());
      imwrite_normalized(filename, image.mappedDepth());

      filename = cv::format("%s/mapped_color.png", frame_dir.c_str());
      imwrite(filename, image.mappedRgb());

      filename = cv::format("%s/depth.yml", frame_dir.c_str());
      imwrite_yml(filename, image.mappedDepth());
    }

    if (!m_only_raw)
    {
      filename = cv::format("%s/raw/depth.png", frame_dir.c_str());
      if (image.rawDepth().data)
        imwrite_normalized(filename.c_str(), image.rawDepth());

      filename = cv::format("%s/depth.png", frame_dir.c_str());
      if (image.depth().data)
        imwrite_normalized(filename.c_str(), image.depth());

      filename = cv::format("%s/intensity.png", frame_dir.c_str());
      if (image.intensity().data)
        imwrite_normalized(filename.c_str(), image.intensity());
    }

    if (image.rawDepth().data)
    {
      if (m_use_binary_raw)
      {
        filename = cv::format("%s/raw/depth.raw", frame_dir.c_str());
        imwrite_Mat1f_raw(filename.c_str(), image.rawDepth());
      }
      else
      {
        filename = cv::format("%s/raw/depth.yml", frame_dir.c_str());
        imwrite_yml(filename.c_str(), image.rawDepth());
      }
    }

    if (image.rawIntensity().data)
    {
      if (m_use_binary_raw)
      {
        filename = cv::format("%s/raw/intensity.raw", frame_dir.c_str());
        imwrite_Mat1f_raw(filename.c_str(), image.rawIntensity());
      }
      else
      {
        filename = cv::format("%s/raw/intensity.yml", frame_dir.c_str());
        imwrite_yml(filename.c_str(), image.rawIntensity());
      }
    }

    if (!m_only_raw)
    {
      filename = cv::format("%s/raw/amplitude.png", frame_dir.c_str());
      if (image.rawAmplitude().data)
        imwrite_normalized(filename.c_str(), image.rawAmplitude());

      filename = cv::format("%s/amplitude.png", frame_dir.c_str());
      if (image.amplitude().data)
        imwrite_normalized(filename.c_str(), image.amplitude());
    }

    if (image.rawAmplitude().data)
    {
      if (m_use_binary_raw)
      {
        filename = cv::format("%s/raw/amplitude.raw", frame_dir.c_str());
        imwrite_Mat1f_raw(filename.c_str(), image.rawAmplitude());
      }
      else
      {
        filename = cv::format("%s/raw/amplitude.yml", frame_dir.c_str());
        imwrite_yml(filename.c_str(), image.rawAmplitude());
      }
    }

    ++m_frame_index;
  }

}
