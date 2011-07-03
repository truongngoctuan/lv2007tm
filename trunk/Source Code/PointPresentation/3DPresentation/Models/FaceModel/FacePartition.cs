using System;
using System.Collections.Generic;
using Microsoft.Xna.Framework.Graphics;
using Microsoft.Xna.Framework;


namespace _3DPresentation.Models.FaceModel
{
    public class FacePartition
    {
        public int ID;
        public List<VertexPositionNormalColor> Vertices;
        public List<ushort> Indices;
        public int PartitionSize;
        private int Current;
        public VertexBuffer VertexBuffer;
        public IndexBuffer IndexBuffer;
        public bool IsValid
        {
            get;
            private set;
        }

        public FacePartition(int partitionSize, int id)
        {
            PartitionSize = partitionSize;
            ID = id;
            Current = 0;
            Vertices = new List<VertexPositionNormalColor>();
            Indices = new List<ushort>();
        }

        public bool IsFull()
        {
            if (Current >= PartitionSize)
                return true;
            return false;
        }

        public int AddPoint(Vector3 point, Color color)
        {
            Vertices.Add(new VertexPositionNormalColor(point, color, new Vector3(0, 0, 0)));
            return Vertices.Count - 1;
        }

        public bool AddIndice(int i1, int i2, int i3)
        {
            if (i1 >= this.PartitionSize || i2 >= this.PartitionSize || i3 >= this.PartitionSize)
                return false;

            Indices.Add(Convert.ToUInt16(i1));
            Indices.Add(Convert.ToUInt16(i2));
            Indices.Add(Convert.ToUInt16(i3));
            Current++;
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

                Vertices[i1].AddNormal(normal);
                Vertices[i2].AddNormal(normal);
                Vertices[i3].AddNormal(normal);
            }

            for (int i = 0; i < Vertices.Count; i++)
            {
                Vertices[i].Normal.Normalize();
            }
        }

        public void InitBuffers(GraphicsDevice graphicsDevice)
        {
            if ((Vertices.Count == 0) || (Indices.Count < 3))
            {
                IsValid = false;
                return;
            }
                
            VertexBuffer = new VertexBuffer(graphicsDevice, VertexPositionNormalColor.VertexDeclaration, Vertices.Count, BufferUsage.WriteOnly);
            VertexBuffer.SetData(0, Vertices.ToArray(), 0, Vertices.Count, 0);

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
