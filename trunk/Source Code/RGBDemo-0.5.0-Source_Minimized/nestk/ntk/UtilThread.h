#pragma once
#include <iostream>
#include <string>
#include <sstream>
using namespace std;

class UtilThread
{
public:
	static std::string IntToString(int i);
};

class thread_adapter
{
public:
    thread_adapter(void (*func)(void*), void* param)
        : _func(func), _param(param)
    {
    }
    void operator()() { _func(_param); }
private:
    void (*_func)(void*);
    void* _param;
};
