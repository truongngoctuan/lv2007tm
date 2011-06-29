#include "Model.h"
#include <string>
using namespace std;

void main()
{
	string strFile = "mesh.ply";
	Model model(strFile);
	model.ExportPCD();
}