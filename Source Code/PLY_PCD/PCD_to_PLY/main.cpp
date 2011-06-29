#include "Model.h"
#include <string>
using namespace std;

void main()
{
	string strFile = "mesh.pcd";
	Model model(strFile);
	model.ExportPLY2();
}