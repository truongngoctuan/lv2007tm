#ifndef MESHMODEL_H
#define MESHMODEL_H

#include <vcg/simplex/vertex/base.h>
#include <vcg/simplex/face/base.h>
#include <vcg/complex/trimesh/base.h>
#include <vcg/simplex/vertex/component_ocf.h>
#include <vcg/simplex/face/component_ocf.h>

// Forward declarations needed for creating the used types
class CVertexO;
class CEdge;
class CFaceO;

// Declaration of the semantic of the used types
class CUsedTypesO: public vcg::UsedTypes < vcg::Use<CVertexO>::AsVertexType,
                                           vcg::Use<CEdge   >::AsEdgeType,
                                           vcg::Use<CFaceO  >::AsFaceType >{};

class CVertexO  : public vcg::Vertex< CUsedTypesO,
  vcg::vertex::InfoOcf,           /*  4b */
  vcg::vertex::Coord3f,           /* 12b */
  vcg::vertex::BitFlags,          /*  4b */
  vcg::vertex::Normal3f,          /* 12b */
  vcg::vertex::Qualityf,          /*  4b */
  vcg::vertex::Color4b,           /*  4b */
  vcg::vertex::VFAdjOcf,          /*  0b */
  vcg::vertex::MarkOcf,           /*  0b */
  vcg::vertex::TexCoordfOcf,      /*  0b */
  vcg::vertex::CurvaturefOcf,     /*  0b */
  vcg::vertex::CurvatureDirfOcf,  /*  0b */
  vcg::vertex::RadiusfOcf         /*  0b */
  >{
};

// The Main Edge Class
// Currently it does not contains anything.
class CEdge : public vcg::Edge<CUsedTypesO, vcg::edge::EVAdj> {
public:
	inline CEdge(){};
  inline CEdge( CVertexO * v0, CVertexO * v1){ V(0)= v0 ; V(1)= v1;};
  static inline CEdge OrderedEdge(CVertexO* v0,CVertexO* v1){
   if(v0<v1) return CEdge(v0,v1);
   else return CEdge(v1,v0);
	}
};

// Each face needs 32 byte, on 32bit arch. and 48 byte on 64bit arch.
class CFaceO    : public vcg::Face<  CUsedTypesO,
      vcg::face::InfoOcf,              /* 4b */
      vcg::face::VertexRef,            /*12b */
      vcg::face::BitFlags,             /* 4b */
      vcg::face::Normal3f,             /*12b */
      vcg::face::QualityfOcf,          /* 0b */
      vcg::face::MarkOcf,              /* 0b */
      vcg::face::Color4bOcf,           /* 0b */
      vcg::face::FFAdjOcf,             /* 0b */
      vcg::face::VFAdjOcf,             /* 0b */
      vcg::face::WedgeTexCoordfOcf     /* 0b */
    > {};


class CMeshO : public vcg::tri::TriMesh< vcg::vertex::vector_ocf<CVertexO>, vcg::face::vector_ocf<CFaceO> >
{
	public :
		int sfn; //The number of selected faces.
		int svn; //The number of selected faces.
		vcg::Matrix44f Tr; // Usually it is the identity. It is applied in rendering and filters can or cannot use it. (most of the filter will ignore this)
		
};

class MeshModel
{
public:
	CMeshO cm;

	public:	
	MeshModel();
};

#endif