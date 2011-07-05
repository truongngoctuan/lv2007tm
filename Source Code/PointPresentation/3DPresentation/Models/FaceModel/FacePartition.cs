using System;
using System.Collections.Generic;
using Microsoft.Xna.Framework.Graphics;
using Microsoft.Xna.Framework;


namespace _3DPresentation.Models.FaceModel
{
    public class FacePartition
    {
        public int ID;
        public List<VertexPositionNormalColor> VerticesList;        
        public List<ushort> IndicesList;

        public VertexPositionNormalColor[] Vertices;
        public ushort[] Indices;

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
            VerticesList = new List<VertexPositionNormalColor>();
            IndicesList = new List<ushort>();
        }

        public bool IsFull()
        {
            if (Current >= PartitionSize)
                return true;
            return false;
        }

        public int AddPoint(Vector3 point, Color color)
        {
            VerticesList.Add(new VertexPositionNormalColor(point, color, new Vector3(0, 0, 0)));
            return VerticesList.Count - 1;
        }

        public bool AddIndice(int i1, int i2, int i3)
        {
            if (i1 >= this.PartitionSize || i2 >= this.PartitionSize || i3 >= this.PartitionSize)
                return false;

            IndicesList.Add(Convert.ToUInt16(i1));
            IndicesList.Add(Convert.ToUInt16(i2));
            IndicesList.Add(Convert.ToUInt16(i3));
            Current++;
            return true;
        }

        public void InitNormals()
        {
            // MUST CONVERT TO ARRAY
            // - VertexPositionNormalColor is a struct => VerticesList[i] : only return a copy of the actual Vertex in List
            //      => any modification'll only affect the copy, not the real one. 
            Vertices = VerticesList.ToArray();

            // release the memory
            VerticesList.Clear(); 
            VerticesList = null;

            for (int i = 0; i < IndicesList.Count / 3; i++)
            {
                int i1 = IndicesList[i * 3];
                int i2 = IndicesList[i * 3 + 1];
                int i3 = IndicesList[i * 3 + 2];
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
            if ((Vertices.Length == 0) || (IndicesList.Count < 3))
            {
                IsValid = false;
                return;
            }

            VertexBuffer = new VertexBuffer(graphicsDevice, VertexPositionNormalColor.VertexDeclaration, Vertices.Length, BufferUsage.WriteOnly);
            VertexBuffer.SetData(0, Vertices, 0, Vertices.Length, 0);

            // optional
            Indices = IndicesList.ToArray();
            IndicesList.Clear(); 
            IndicesList = null;

            IndexBuffer = new IndexBuffer(graphicsDevice, IndexElementSize.SixteenBits, Indices.Length, BufferUsage.WriteOnly);
            IndexBuffer.SetData(0, Indices, 0, Indices.Length);

            IsValid = true;
            Vertices = null;
            Indices = null;
        }

        public IndexBuffer GetIndexBuffer()
        {
            return IndexBuffer;
        }
    }
}
