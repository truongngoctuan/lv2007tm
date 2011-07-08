using System.Collections.Generic;
using System.Diagnostics;
using Microsoft.Xna.Framework;

namespace Babylon
{
    [DebuggerDisplay("Name = {parent.Name} ID = {materialID}")]
    public class SubModel
    {
        readonly Model parent;
        readonly int minVertexIndex;
        readonly int startIndex;
        readonly int facesCount;
        readonly int verticesCount;
        readonly int materialID;
        BoundingInfo boundingInfo;
        int[] indices;
        readonly Dictionary<CollisionSystem, Vector3[]> worldVertices;
        readonly Dictionary<CollisionSystem, Matrix> transformationMatrices; 
        bool positionOnlyDatasDefined;
        int positionOnlyVertexStart;
        int positionOnlyVertexCount;

        public float DistanceToActiveCamera { get; set; }

        internal Dictionary<CollisionSystem, Vector3[]> WorldVertices
        {
            get
            {
                return worldVertices;
            }
        }

        internal Dictionary<CollisionSystem, Matrix> TransformationMatrices
        {
            get
            {
                return transformationMatrices;
            }
        }

        public Model Parent
        {
            get { return parent; }
        }

        public Material Material
        {
            get
            {
                return parent.Material.GetEffectiveMaterial(materialID);
            }
        }

        public float Alpha
        {
            get
            {
                return parent.Material.Alpha * Parent.Visibility;
            }
        }

        public int MinVertexIndex
        {
            get { return minVertexIndex; }
        }

        public int StartIndex
        {
            get { return startIndex; }
        }

        public int FacesCount
        {
            get { return facesCount; }
        }

        public int VerticesCount
        {
            get { return verticesCount; }
        }

        public BoundingInfo BoundingInfo
        {
            get { return boundingInfo; }
        }

        internal SubModel(Model parent, int materialID, int minVertexIndex, int startIndex, int facesCount, int verticesCount)
        {
            this.parent = parent;
            this.materialID = materialID;
            this.minVertexIndex = minVertexIndex;
            this.startIndex = startIndex;
            this.facesCount = facesCount;
            this.verticesCount = verticesCount;

            worldVertices = new Dictionary<CollisionSystem, Vector3[]>();
            transformationMatrices = new Dictionary<CollisionSystem, Matrix>();
        }

        internal void PrepareSubModel()
        {
            Vector3[] points = new Vector3[verticesCount];
            for (int index = 0; index < verticesCount; index++)
            {
                points[index] = parent.Points[minVertexIndex + index];
            }

            indices = new int[facesCount * 3];
            for (int index = 0; index < facesCount * 3; index++)
            {
                indices[index] = parent.Indices[startIndex + index];
            }

            boundingInfo = new BoundingInfo(points);
        }

        void ComputePositionOnlyDatas()
        {
            positionOnlyDatasDefined = true;
            if (Parent.Points.Length == Parent.VerticesCount)
            {
                positionOnlyVertexStart = minVertexIndex;
                positionOnlyVertexCount = VerticesCount;
                return;
            }
            positionOnlyVertexStart = parent.VerticesCount;
            int max = 0;

            for (int index = StartIndex ; index < StartIndex + FacesCount * 3; index++)
            {
                int vertexIndex = (int)Parent.Indices[index];

                if (vertexIndex < positionOnlyVertexStart)
                    positionOnlyVertexStart = vertexIndex;

                if (vertexIndex > max)
                    max = vertexIndex;
            }

            positionOnlyVertexCount = max - positionOnlyVertexStart + 1;
        }

        internal int PositionOnlyVertexStart
        {
            get
            {
                if (!positionOnlyDatasDefined)
                    ComputePositionOnlyDatas();

                return positionOnlyVertexStart;
            }
        }

        internal int PositionOnlyVertexCount
        {
            get
            {
                if (!positionOnlyDatasDefined)
                    ComputePositionOnlyDatas();

                return positionOnlyVertexCount;
            }
        }
    }
}
 