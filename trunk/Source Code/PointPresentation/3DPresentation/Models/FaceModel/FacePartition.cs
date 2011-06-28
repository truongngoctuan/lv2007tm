using System;
using System.Collections.Generic;
using Microsoft.Xna.Framework.Graphics;
using Microsoft.Xna.Framework;


namespace _3DPresentation.Models.FaceModel
{
    public class FacePartition
    {
        private VertexPositionNormalColor[] Vertices;
        private List<ushort> Indices;
        public int PartitionSize;
        private int Current;
        public VertexBuffer VertexBuffer;
        public IndexBuffer IndexBuffer;
        public bool IsValid
        {
            get;
            private set;
        }

        public FacePartition(int partitionSize)
        {
            PartitionSize = partitionSize;
            Current = 0;
            Vertices = new VertexPositionNormalColor[PartitionSize];
            Indices = new List<ushort>();
        }

        Random r = new Random();
        public bool AddPoint(Vector3 point, Color color)
        {
            if (Current >= PartitionSize)
                return false;

            Vertices[Current++] = new VertexPositionNormalColor(point, color, new Vector3(0, 0, 0));
            return true;
        }

        public bool AddIndice(int i1, int i2, int i3)
        {
            if (i1 > 65535 || i2 > 65535 || i3 > 65535)
                return false;

            Indices.Add(Convert.ToUInt16(i1));
            Indices.Add(Convert.ToUInt16(i2));
            Indices.Add(Convert.ToUInt16(i3));
            return true;
        }

        public void InitNormals()
        {
            for (int i = 0; i < Indices.Count / 3; i++)
            {
                int i1 = Indices[i];
                int i2 = Indices[i + 1];
                int i3 = Indices[i + 2];
                Vector3 v1 = Vertices[i2].Position - Vertices[i1].Position;
                Vector3 v2 = Vertices[i3].Position - Vertices[i1].Position;
                Vector3 normal = Vector3.Cross(v2, v1);

                Vertices[i1].Normal += normal;
                Vertices[i2].Normal += normal;
                Vertices[i3].Normal += normal;
            }

            for (int i = 0; i < Vertices.Length; i++)
            {
                Vertices[i].Normal.Normalize();
            }
        }

        public void InitBuffers(GraphicsDevice graphicsDevice)
        {
            if ((Vertices.Length == 0) || (Indices.Count < 3))
            {
                IsValid = false;
                return;
            }
                
            VertexBuffer = new VertexBuffer(graphicsDevice, VertexPositionNormalColor.VertexDeclaration, Vertices.Length, BufferUsage.WriteOnly);
            VertexBuffer.SetData(0, Vertices, 0, Vertices.Length, 0);

            IndexBuffer = new IndexBuffer(graphicsDevice, IndexElementSize.SixteenBits, Indices.Count, BufferUsage.WriteOnly);
            IndexBuffer.SetData(0, Indices.ToArray(), 0, Indices.Count);

            IsValid = true;
        }

        public IndexBuffer GetIndexBuffer()
        {
            return IndexBuffer;
        }
    }
}
