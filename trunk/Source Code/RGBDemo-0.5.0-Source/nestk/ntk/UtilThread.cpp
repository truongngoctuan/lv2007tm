#include "UtilThread.h"

std::string UtilThread::IntToString(int i)
{
    std::stringstream ss;
    std::string s;
    ss << i;
    s = ss.str();

    return s;
}