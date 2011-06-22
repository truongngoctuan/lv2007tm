#include "file_grabber2.h"

file_grabber2::file_grabber2(void)
{
}

file_grabber2::~file_grabber2(void)
{
}

file_grabber2::file_grabber2(const std::string& path)
  : m_path(path.c_str()),
    m_current_image_index(0)
{
    m_image_list = m_path.entryList(QStringList("view????"), QDir::Dirs, QDir::Name);
    //ntk_ensure(!m_image_list.empty(), "No view???? images in given directory.");
}


bool file_grabber2::GetNextImage()
{
	if (m_current_image_index >= m_image_list.size())
        //m_current_image_index = 0;
		return false;

      QString filepath = m_path.absoluteFilePath(m_image_list[m_current_image_index]);
      //{
        //QWriteLocker locker(&m_lock);
        m_buffer_image.loadFromDir(filepath.toStdString(), m_calib_data);
      //}
      ++m_current_image_index;
	  return true;
}

  void file_grabber2 :: copyImageTo(RGBDImage& image)
  {
    //QReadLocker locker(&m_lock);
    m_buffer_image.copyTo(image);
  }