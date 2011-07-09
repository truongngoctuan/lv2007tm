using System;
using System.Collections.Generic;
using Microsoft.Xna.Framework.Graphics;
using Microsoft.Xna.Framework;


namespace _3DPresentation.Models
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
        }

        public bool IsFull()
        {
            if (Current >= PartitionSize)
                return true;
            return false;
        }

        public void Begin()
        {
            VerticesList = new List<VertexPositionNormalColor>();
            IndicesList = new List<ushort>();
            Current = 0;
        }

        public void End()
        {
            Vertices = VerticesList.ToArray();
            // release the memory
            VerticesList.Clear(); 
            VerticesList = null;

            Indices = IndicesList.ToArray();
            IndicesList.Clear(); 
            IndicesList = null;
        }

        public int AddPoint(Vector3 point, Color color)
        {
            VerticesList.Add(new VertexPositionNormalColor(point, color, new Vector3(0, 0, 0)));
            return VerticesList.Count - 1;
        }

        private int maxIndex = -1;
        private int maxI = -1;
        public bool AddIndice(int i1, int i2, int i3)
        {
            if (i1 >= this.PartitionSize || i2 >= this.PartitionSize || i3 >= this.PartitionSize)
                return false;

            IndicesList.Add(Convert.ToUInt16(i1));
            IndicesList.Add(Convert.ToUInt16(i2));
            IndicesList.Add(Convert.ToUInt16(i3));
            Current++;

            if (Convert.ToUInt16(i1) > maxIndex) { maxIndex = Convert.ToUInt16(i1); maxI = i1; }
            if (Convert.ToUInt16(i2) > maxIndex) { maxIndex = Convert.ToUInt16(i2); maxI = i2; }
            if (Convert.ToUInt16(i3) > maxIndex) { maxIndex = Convert.ToUInt16(i3); maxI = i3; }
            return true;
        }

        public void InitNormals()
        {
            // MUST USE VERTICES ARRAY
            // - VertexPositionNormalColor is a struct => VerticesList[i] : only return a copy of the actual Vertex in List
            //      => any modification'll only affect the copy, not the real one.            

            for (int i = 0; i < Indices.Length / 3; i++)
            {
                int i1 = Indices[i * 3];
                int i2 = Indices[i * 3 + 1];
                int i3 = Indices[i * 3 + 2];
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
            if ((Vertices.Length == 0) || (Indices.Length < 3))
            {
                IsValid = false;
                return;
            }

            VertexBuffer = new VertexBuffer(graphicsDevice, VertexPositionNormalColor.VertexDeclaration, Vertices.Length, BufferUsage.WriteOnly);
            VertexBuffer.SetData(0, Vertices, 0, Vertices.Length, 0);
            
            IndexBuffer = new IndexBuffer(graphicsDevice, IndexElementSize.SixteenBits, Indices.Length, BufferUsage.WriteOnly);
            IndexBuffer.SetData(0, Indices, 0, Indices.Length);

            //Vertices = null;
            //Indices = null;
            IsValid = true;
        }

        public void Render(GraphicsDevice graphicsDevice)
        {
            if (IsValid == false)
                return;

            graphicsDevice.SetVertexBuffer(VertexBuffer);
            graphicsDevice.Indices = IndexBuffer;

            graphicsDevice.DrawIndexedPrimitives(PrimitiveType.TriangleList, 0, 0, VertexBuffer.VertexCount, 0, IndexBuffer.IndexCount / 3);
        }
    }
}
