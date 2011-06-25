#pragma once
#include <boost/thread.hpp>
#include <queue>

using namespace std;
using namespace boost;
using namespace boost::this_thread;

// Queue class that has thread synchronisation
template <typename T>
class SynchronisedQueue
{
private:
	std::queue<T> m_queue;						// Use STL queue to store data
	boost::mutex m_mutex;						// The mutex to synchronise on
	boost::condition_variable m_cond;		// The condition to wait for
	int m_index;
	int m_iMaxQueueElement;
public:
SynchronisedQueue()
{
	m_index = 0;
	m_iMaxQueueElement = 1;
}
void SetMaxQueueElement(int i)
{
	m_iMaxQueueElement = i;
}
bool CheckNeedToEnqueue()
{
	boost::unique_lock<boost::mutex> lock(m_mutex);
	if (m_queue.size() < m_iMaxQueueElement)
	{
		return true;
	}
	return false;
}

	// Add data to the queue and notify others
	void Enqueue(const T& data)
	{
		// Acquire lock on the queue
		boost::unique_lock<boost::mutex> lock(m_mutex);

		// Add the data to the queue
		m_queue.push(data);

		// Notify others that data is ready
		m_cond.notify_one();

	} // Lock is automatically released here

	// Get data from the queue. Wait for data if not available
	T Dequeue(int &i)
	{

		// Acquire lock on the queue
		boost::unique_lock<boost::mutex> lock(m_mutex);

		// When there is no data, wait till someone fills it.
		// Lock is automatically released in the wait and obtained 
		// again after the wait
		while (m_queue.size()==0) m_cond.wait(lock);

		// Retrieve the data from the queue
		T result=m_queue.front(); m_queue.pop();
		
		i = m_index;

		cout<<"dequeue times: "<<m_index++<<" still have "<<m_queue.size()<<" in queue"<<endl;
			
		return result;

	} // Lock is automatically released here
};
