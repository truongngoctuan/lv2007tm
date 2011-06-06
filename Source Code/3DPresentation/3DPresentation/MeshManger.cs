using System.Collections.Generic;
using Microsoft.Xna.Framework;
using Microsoft.Xna.Framework.Graphics;
using System.Text;
using System.Windows.Threading;
using System;

namespace _3DPresentation
{
    public class MeshManger
    {
        private static int PARTITION_BASE_WIDTH = 100; 
        private static int PARTITION_BASE_HEIGHT = 100; 

        public List<Partition> Partitions;
        int MeshWidth;
        int MeshHeight;

        public int PartitionWidth;
        public int PartitionHeight;
        public int PartitionRealWidth;
        public int PartitionRealHeight;

        public MeshManger()
        {
            MeshWidth = MeshHeight = 0;
            Partitions = new List<Partition>();
        }

        #region SetUp
        public void Begin(int modelWidth, int modelHeight)
        {
            if (modelWidth < 2 || modelHeight < 2)
                return; // throw exception           
 
            PartitionWidth = PARTITION_BASE_WIDTH < modelWidth ? PARTITION_BASE_WIDTH : modelWidth;
            PartitionHeight = PARTITION_BASE_HEIGHT < modelHeight ? PARTITION_BASE_HEIGHT : modelHeight;

            PartitionRealWidth = PartitionWidth + 1;
            PartitionRealHeight = PartitionHeight + 1;

            MeshWidth = (modelWidth + PartitionWidth - 2) / PartitionWidth;
            MeshHeight = (modelHeight + PartitionHeight - 2) / PartitionHeight;

            for (int i = 0; i < MeshWidth * MeshHeight; i++)
            {
                Partitions.Add(new Partition(PartitionWidth, PartitionHeight, PartitionRealWidth, PartitionRealHeight));
            }
        }

        private void PixelToCoordinate(int pixelRow, int pixelCol, out int partitionRow, out int partitionCol, out int vertexRow, out int vertexCol)
        {
            partitionRow = pixelRow / PartitionHeight;
            partitionCol = pixelCol / PartitionWidth;
            vertexRow = pixelRow % PartitionHeight;
            vertexCol = pixelCol % PartitionWidth;
        }

        public void AddVertex(VertexPositionNormalColor vertex, int pixelRow, int pixelCol)
        {
            int partitionRow, partitionCol, vertexRow, vertexCol;
            PixelToCoordinate(pixelRow, pixelCol, out partitionRow, out partitionCol, out vertexRow, out vertexCol);

            Partition partition = Partitions[partitionCol + partitionRow * MeshWidth];
            partition.AddVertex(vertex, vertexRow, vertexCol);
        }

        public void End()
        {
            // Fill in the bounders (reserved col, row)
            for(int index = 0; index < Partitions.Count; index++)
            {
                int row = index / MeshWidth;
                int col = index % MeshWidth;
                if(row + 1 < MeshHeight)
                {
                    // copy first row of the below partition, to the reserve row of the current 
                    int belowIndex = index + MeshWidth;
                    Partitions[index].FillTheGap(Partitions[belowIndex], Partition.GapType.BOT);
                }

                if (col + 1 < MeshWidth)
                {
                    // copy first col of the right partition, to the reserve col of the current
                    int rightIndex = index + 1;
                    Partitions[index].FillTheGap(Partitions[rightIndex], Partition.GapType.RIGHT);
                }

                if (row + 1 < MeshHeight && col + 1 < MeshWidth)
                {
                    int rightbelow = index + MeshWidth + 1;
                    Partitions[index].FillTheGap(Partitions[rightbelow], Partition.GapType.RIGHT_BOT);
                }
            }

            // Calculate normal vector
            for (int i = 0; i < Partitions.Count; i++)
            {
                Partitions[i].CalculateNormalVector(GlobalVars.LOD.HIGH);
            }
        }

        public void InitVertexBuffer(GraphicsDevice graphicsDevice)
        {
            for (int i = 0; i < Partitions.Count; i++)
            {
                Partitions[i].InitBuffer(graphicsDevice);
            }
        }
        #endregion

        static VertexBuffer sVertexBuffer = null;
        static IndexBuffer sIndexBuffer = null;
        #region Render
        public void RenderPartition(GraphicsDevice graphicsDevice, int partitionIndex)
        {
            VertexBuffer vertexBuffer = Partitions[partitionIndex].VertexBuffer;
            IndexBuffer indexBuffer = Partitions[partitionIndex].GetIndexBuffer(_3DPresentation.GlobalVars.LevelOfDetail, graphicsDevice);
            /*
            if (sVertexBuffer == null)
            {
                sVertexBuffer = Partitions[partitionIndex].VertexBuffer;
            }
            if (sIndexBuffer == null)
            {
                sIndexBuffer = Partitions[partitionIndex].GetIndexBuffer(Partition.LOD.HIGH, graphicsDevice);
            }
            VertexBuffer vertexBuffer = sVertexBuffer;
            IndexBuffer indexBuffer = sIndexBuffer;
            */
            graphicsDevice.SetVertexBuffer(vertexBuffer);
            graphicsDevice.Indices = indexBuffer;
            graphicsDevice.DrawIndexedPrimitives(PrimitiveType.TriangleList, 0, 0, Partitions[partitionIndex].Length, 0, indexBuffer.IndexCount / 3);
        }
        #endregion
    }
}
