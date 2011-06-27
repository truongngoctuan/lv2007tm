//#include "Logger.h"
//
//void Logger::Begin()
//{
//	pDebug = ofstream("log.txt");
//}
//void Logger::Push(string str)
//{
//	if(!pDebug)
//		pDebug << str.c_str();// << endl;
//}
//void Logger::End()
//{
//	if(pDebug.is_open())
//		pDebug.close();
//}
//
//ofstream& Logger::GetDebugStream()
//{
//	return pDebug;
//}