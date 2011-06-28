using System;
using System.Collections.Generic;
using Microsoft.Xna.Framework;
using Microsoft.Xna.Framework.Graphics;


namespace _3DPresentation.Models.FaceModel
{
    public class FaceManager
    {
        private static int PARTITION_BASE_SIZE = 10000;

        public List<FacePartition> Partitions;
        public int PartitionSize;
        public int NumPoints;
        public int iCurrentPartition;
        public FaceManager()
        {
            Partitions = new List<FacePartition>();
        }

        public void Begin(int nPoints)
        {
            NumPoints = nPoints;
            PartitionSize = PARTITION_BASE_SIZE < nPoints ? PARTITION_BASE_SIZE : nPoints;
            int nPartitions = (nPoints + PartitionSize - 1) / PartitionSize;
            for (int i = 0; i < nPartitions; i++)
            {
                Partitions.Add(new FacePartition(PartitionSize));
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

        private bool indexToPartition(ref int index, out int partitionID)
        {
            bool result = false;            
            int stackup = -1;
            partitionID = -1;
            for(int i = 0; i < Partitions.Count; i++)
            {
                if(stackup + Partitions[i].PartitionSize > index)
                {
                    partitionID = i;
                    index -= stackup;
                    result = true;
                    break;
                }                
                stackup += Partitions[i].PartitionSize;
            }            
            return result;
        }
        public bool AddIndice(int i1, int i2, int i3)
        {
            int partitionID1, partitionID2, partitionID3;
            if (!indexToPartition(ref i1, out partitionID1))
                return false;
            if (!indexToPartition(ref i2, out partitionID2))
                return false;
            if (!indexToPartition(ref i3, out partitionID3))
                return false;

            if (partitionID1 == partitionID2 && partitionID1 == partitionID3)
            {
                if (partitionID1 == 109)
                    partitionID1 = partitionID2;
                return Partitions[partitionID1].AddIndice(i1, i2, i3);
            }

            return false;
        }

        public void End()
        {
            foreach (FacePartition partition in Partitions)
                partition.InitNormals();
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
            if (Partitions[partitionIndex].IsValid == false)
                return;
            VertexBuffer vertexBuffer = Partitions[partitionIndex].VertexBuffer;
            IndexBuffer indexBuffer = Partitions[partitionIndex].GetIndexBuffer();

            graphicsDevice.SetVertexBuffer(vertexBuffer);
            graphicsDevice.Indices = indexBuffer;

            graphicsDevice.DrawIndexedPrimitives(PrimitiveType.TriangleList, 0, 0, vertexBuffer.VertexCount, 0, indexBuffer.IndexCount / 3);
        }
    }
}
