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

#ifndef   	NTK_UTILS_TIME_H_
# define   	NTK_UTILS_TIME_H_

# include <ntk/core.h>
# include <ntk/utils/debug.h>
//# include <QMutex>
//# include <QWaitCondition>
# include <iostream>
# include <string>

namespace ntk
{
  
  //inline void sleep(int msecs)
  //{
  //  // FIXME: really hacky!
  //  QMutex mutex; mutex.lock();
  //  QWaitCondition cond;
  //  cond.wait(&mutex, msecs);
  //  mutex.unlock();
  //}

  class Time
  {
  public:
    static unsigned long getMillisecondCounter() { return 1000.0*cv::getTickCount()/cv::getTickFrequency(); }
  };

  class TimeCount
  {
  public:
    TimeCount(const std::string& name, int debug_level = 1)
      : m_name(name),
        m_start(ntk::Time::getMillisecondCounter()),
        m_debug_level(debug_level)
    {
    }

    unsigned long elapsedMsecs() const { return ntk::Time::getMillisecondCounter()-m_start; }

    void stop(const std::string& marker = "")
    {
      unsigned long tstop = ntk::Time::getMillisecondCounter();
      ntk_dbg(m_debug_level) << "[TIME] elapsed in " << m_name << marker << ": " << (float(tstop)-m_start) << " msecs";
	  cout << "[TIME] elapsed in " << m_name << marker << ": " << (float(tstop)-m_start) << " msecs"<<endl;
    }

  private:
    std::string m_name;
    unsigned long m_start;
    int m_debug_level;
  };

  
  class TimeCountThread
  {
  public:
    TimeCountThread(int iThreadId, const std::string& name, int debug_level = 1)
      : m_iThread_Id(iThreadId),
	  m_name(name),
        m_start(ntk::Time::getMillisecondCounter()),
        m_debug_level(debug_level)
    {
    }

    unsigned long elapsedMsecs() const { return ntk::Time::getMillisecondCounter()-m_start; }

    void stop(const std::string& marker = "")
    {
      unsigned long tstop = ntk::Time::getMillisecondCounter();
      //ntk_dbg(m_debug_level) << "[TIME] elapsed in " << m_name << marker << ": " << (float(tstop)-m_start) << " msecs";
	  cout << "[TIME] [Thread "<<m_iThread_Id<<"] elapsed in " << m_name << marker << ": " << (float(tstop)-m_start) << " msecs"<<endl;
    }

  private:
    std::string m_name;
    unsigned long m_start;
    int m_debug_level;
	int m_iThread_Id;
  };

} // end of ntk

#endif 	    /* !NTK_UTILS_TIME_H_ */
