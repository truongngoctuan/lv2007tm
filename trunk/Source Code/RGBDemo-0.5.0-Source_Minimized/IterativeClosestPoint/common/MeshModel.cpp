#include "MeshModel.h"

using namespace vcg;

MeshModel::MeshModel() 
{
	//_id=parent->newMeshId();
	// These data are always active on the mesh
	cm.Tr.SetIdentity();
	cm.sfn=0;
	cm.svn=0;
}
