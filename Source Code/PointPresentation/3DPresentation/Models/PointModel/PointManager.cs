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

        public bool ExportVertexData(BaseModel.FileType fileType, BaseModel.VertexTypes vertexType, StreamWriter writer, Matrix worldMatrix)
        {
            if (writer == null)
                return false;
            bool result = true;
            for (int i = 0; i < Partitions.Count; i++)
            {
                if (Partitions[i].ExportVertexData(fileType, vertexType, writer, worldMatrix) == false)
                    result = false;
            }
            return result;
        }

        public bool ExportIndiceData(BaseModel.FileType fileType, BaseModel.VertexTypes vertexType, StreamWriter writer, Matrix worldMatrix, long offset)
        {
            if (writer == null)
                return false;

            bool result = true;
            for (int i = 0; i < Partitions.Count; i++)
            {
                if (Partitions[i].ExportIndiceData(fileType, vertexType, writer, worldMatrix, offset) == false)
                    result = false;
            }
            return result;
        }

        public void projectToImagePlane(Matrix mat, int iWidth, int iHeight, int[,] zBuffer, System.Windows.Media.Imaging.WriteableBitmap bm)
        {
            for (int i = 0; i < Partitions.Count; i++)
            {
                Partitions[i].projectToImagePlane(mat, iWidth, iHeight, zBuffer, bm);
            }

        }
    }
}
