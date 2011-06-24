using System;
using System.Collections.Generic;
using Microsoft.Xna.Framework;
using Microsoft.Xna.Framework.Graphics;


namespace _3DPresentation.Models.PointModel
{
    public class PointManager
    {
        private static int PARTITION_BASE_SIZE = 250;

        public List<PointPartition> Partitions;
        public int PartitionSize;
        public int NumPoints;
        public int iCurrentPartition;
        public PointManager()
        {
            Partitions = new List<PointPartition>();
        }

        public void Begin(int nPoints)
        {
            NumPoints = nPoints;
            PartitionSize = PARTITION_BASE_SIZE < nPoints ? PARTITION_BASE_SIZE : nPoints;
            int nPartitions = (nPoints + PartitionSize - 1) / PartitionSize;
            for (int i = 0; i < nPartitions; i++)
            {
                Partitions.Add(new PointPartition(PartitionSize));
            }
        }

        public bool AddPoint(Vector3 vertex, Color color)
        {
            if (iCurrentPartition >= Partitions.Count)
                return false;

            if(Partitions[iCurrentPartition].AddPoint(vertex, color) == true)
                return true;

            iCurrentPartition++;
            return AddPoint(vertex, color);
        }

        public void End()
        {
        }

        public void InitBuffers(GraphicsDevice graphicsDevice)
        {
            for (int i = 0; i < Partitions.Count; i++)
            {
                Partitions[i].InitBuffers(graphicsDevice);
            }
        }

        public void RenderPartition(GraphicsDevice graphicsDevice, int partitionIndex)
        {
            VertexBuffer vertexBuffer = Partitions[partitionIndex].VertexBuffer;
            IndexBuffer indexBuffer = Partitions[partitionIndex].GetIndexBuffer();

            graphicsDevice.SetVertexBuffer(vertexBuffer);
            graphicsDevice.Indices = indexBuffer;

            graphicsDevice.DrawIndexedPrimitives(PrimitiveType.TriangleList, 0, 0, vertexBuffer.VertexCount, 0, indexBuffer.IndexCount / 3);
        }
    }
}
