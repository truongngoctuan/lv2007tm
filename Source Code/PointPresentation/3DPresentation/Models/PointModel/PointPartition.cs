using System;
using System.Collections.Generic;
using Microsoft.Xna.Framework.Graphics;
using Microsoft.Xna.Framework;


namespace _3DPresentation.Models
{
    public class PointPartition
    {
        private VertexPositionOffsetColor[] Vertices;
        private ushort[] Indices;
        public int PartitionSize;
        private int Current;
        public VertexBuffer VertexBuffer;
        public IndexBuffer IndexBuffer;

        public bool IsValid
        {
            get;
            private set;
        }

        public PointPartition(int partitionSize)
        {
            PartitionSize = partitionSize;
            Current = 0;                    
        }

        public void Begin()
        {
            Vertices = new VertexPositionOffsetColor[PartitionSize * 4];
            Indices = new ushort[PartitionSize * 6];
        }

        public bool AddPoint(Vector3 position, Color color)
        {
            if (Current >= PartitionSize * 4)
                return false;

            //color = new Color((float)r.NextDouble(), (float)r.NextDouble(), (float)r.NextDouble(), 1f);
            //point = new Vector3((float)r.NextDouble() - 0.5f, (float)r.NextDouble() - 0.5f, (float)r.NextDouble() - 0.5f);

            Vertices[Current++] = new VertexPositionOffsetColor(position, new Vector2(-1.0f, -1.0f), color);
            Vertices[Current++] = new VertexPositionOffsetColor(position, new Vector2(-1.0f, 1.0f), color);
            Vertices[Current++] = new VertexPositionOffsetColor(position, new Vector2(1.0f, -1.0f), color);
            Vertices[Current++] = new VertexPositionOffsetColor(position, new Vector2(1.0f, 1.0f), color);
            return true;
        }

        public void End()
        {
            ushort index = 0;
            for (int i = 0; i < Indices.Length; )
            {
                // clockwise triangle
                Indices[i++] = index++;
                Indices[i++] = index++;
                Indices[i++] = index--;

                // counter-clockwise triangle
                Indices[i++] = index++;
                Indices[i++] = index++;
                Indices[i++] = index++;
            }
        }

        public void InitBuffers(GraphicsDevice graphicsDevice)
        {
            if ((Vertices.Length == 0) || (Indices.Length < 3))
            {
                IsValid = false;
                return;
            }

            VertexBuffer = new VertexBuffer(graphicsDevice, VertexPositionOffsetColor.VertexDeclaration, Vertices.Length, BufferUsage.WriteOnly);
            VertexBuffer.SetData(0, Vertices, 0, Vertices.Length, 0);

            IndexBuffer = new IndexBuffer(graphicsDevice, IndexElementSize.SixteenBits, Indices.Length, BufferUsage.WriteOnly);
            IndexBuffer.SetData(0, Indices, 0, Indices.Length);

            Vertices = null;
            Indices = null;
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
