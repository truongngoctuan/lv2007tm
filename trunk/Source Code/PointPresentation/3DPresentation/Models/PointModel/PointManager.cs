using System;
using System.Collections.Generic;
using Microsoft.Xna.Framework;
using Microsoft.Xna.Framework.Graphics;
using System.IO;


namespace _3DPresentation.Models
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

            for (int i = 0; i < Partitions.Count; i++)
            {
                Partitions[i].Begin();
            }
        }

        public bool AddVertex(Vector3 position, Color color)
        {
            if (iCurrentPartition >= Partitions.Count)
                return false;

            if(Partitions[iCurrentPartition].AddPoint(position, color) == true)
                return true;

            iCurrentPartition++;
            return AddVertex(position, color);
        }

        public void End()
        {
            for (int i = 0; i < Partitions.Count; i++)
            {
                Partitions[i].End();
            }
        }

        public void InitBuffers(GraphicsDevice graphicsDevice)
        {
            for (int i = 0; i < Partitions.Count; i++)
            {
                Partitions[i].InitBuffers(graphicsDevice);
            }
        }

        public void Render(GraphicsDevice graphicsDevice)
        {
            for (int i = 0; i < Partitions.Count; i++)
            {
                Partitions[i].Render(graphicsDevice);
            }
        }

        public bool Export_PLY(StreamWriter writer, Matrix worldMatrix)
        {
            if (writer == null)
                return false;
            bool result = true;
            for (int i = 0; i < Partitions.Count; i++)
            {
                Partitions[i].Export_PLY(writer, worldMatrix);
            }
            return result;
        }
    }
}
