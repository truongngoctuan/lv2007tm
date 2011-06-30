#pragma once
#include <string>

class PCL_Write
{
public:
	PCL_Write(void);
	~PCL_Write(void);

public:
	static __declspec(dllexport) bool Auto(std::string strPCDFile);
};

