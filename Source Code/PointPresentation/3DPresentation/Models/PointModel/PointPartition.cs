using System;
using System.Collections.Generic;
using Microsoft.Xna.Framework.Graphics;
using Microsoft.Xna.Framework;


namespace _3DPresentation.Models.PointModel
{
    public class PointPartition
    {
        private VertexPositionOffsetColor[] Vertices;
        public int PartitionSize;
        private int Current;
        public VertexBuffer VertexBuffer;
        public IndexBuffer IndexBuffer;

        public PointPartition(int partitionSize)
        {
            PartitionSize = partitionSize;
            Current = 0;
            Vertices = new VertexPositionOffsetColor[PartitionSize * 4];            
        }

        Random r = new Random();
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

        public void InitBuffers(GraphicsDevice graphicsDevice)
        {
            VertexBuffer = new VertexBuffer(graphicsDevice, VertexPositionOffsetColor.VertexDeclaration, Vertices.Length, BufferUsage.WriteOnly);
            VertexBuffer.SetData(0, Vertices, 0, Vertices.Length, 0);

            ushort[] indices = new ushort[PartitionSize * 6];
            ushort index = 0;
            for (int i = 0; i < indices.Length;)
            {
                // clockwise triangle
                indices[i++] = index++;
                indices[i++] = index++;
                indices[i++] = index--;

                // counter-clockwise triangle
                indices[i++] = index++;
                indices[i++] = index++;
                indices[i++] = index++;
            }
            IndexBuffer = new IndexBuffer(graphicsDevice, IndexElementSize.SixteenBits, indices.Length, BufferUsage.WriteOnly);
            IndexBuffer.SetData(0, indices, 0, indices.Length);
        }

        public IndexBuffer GetIndexBuffer()
        {
            return IndexBuffer;
        }
    }
}
