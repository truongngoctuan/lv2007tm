using System;
using System.Collections.Generic;
using Microsoft.Xna.Framework;
using Microsoft.Xna.Framework.Graphics;
using System.IO;


namespace _3DPresentation.Models
{
    public class TexCoordManager
    {
        public class Node
        {
            public Vector3 Position;
            public int lastPartition;
            public int lastIndex;

            public Node(Vector3 position)
            {
                Position = position;
                lastPartition = -1;
                lastIndex = -1;
            }
        }

        private static int PARTITION_BASE_SIZE = 2500;

        public List<TexCoordPartition> Partitions;
        public int PartitionSize;
        public int NumPoints;
        public int NumFaces;

        Node[] nodes;

        public TexCoordManager()
        {
            Partitions = new List<TexCoordPartition>();
        }

        public void Begin(int nPoints, int nFaces)
        {
            NumPoints = nPoints;
            NumFaces = nFaces;
            PartitionSize = PARTITION_BASE_SIZE < nFaces ? PARTITION_BASE_SIZE : nFaces;
            int nPartitions = (nFaces + PartitionSize - 1) / PartitionSize;
            for (int i = 0; i < nPartitions; i++)
            {
                Partitions.Add(new TexCoordPartition(PartitionSize, i));
            }

            nodes = new Node[nPoints];

            for (int i = 0; i < Partitions.Count; i++)
            {
                Partitions[i].Begin();
            }
        }

        int iCurrentNode = 0;
        public bool AddVertex(Vector3 position)
        {
            if (iCurrentNode >= nodes.Length)
                return false;
            nodes[iCurrentNode++] = new Node(position);
            return true;
        }

        int iCurrentPartition = 0;
        public bool AddIndice(int i1, int i2, int i3, Vector2 texCoord1, Vector2 texCoord2, Vector2 texCoord3)
        {
            if (i1 == i2 || i2 == i3 || i1 == i3)
                return false;
            bool result = false;
            while(iCurrentPartition < Partitions.Count)
            {
                TexCoordPartition partition = Partitions[iCurrentPartition];
                if(partition.IsFull())
                {
                    iCurrentPartition++;
                }
                else
                {
                    if(nodes[i1].lastPartition != Partitions[iCurrentPartition].ID)
                    {
                        nodes[i1].lastPartition = partition.ID;
                        nodes[i1].lastIndex = partition.AddPoint(nodes[i1].Position, texCoord1);
                    }
                    if (nodes[i2].lastPartition != Partitions[iCurrentPartition].ID)
                    {
                        nodes[i2].lastPartition = partition.ID;
                        nodes[i2].lastIndex = partition.AddPoint(nodes[i2].Position, texCoord2);
                    }
                    if (nodes[i3].lastPartition != Partitions[iCurrentPartition].ID)
                    {
                        nodes[i3].lastPartition = partition.ID;
                        nodes[i3].lastIndex = partition.AddPoint(nodes[i3].Position, texCoord3);
                    }
                    partition.AddIndice(nodes[i1].lastIndex, nodes[i2].lastIndex, nodes[i3].lastIndex);
                    result = true;
                    break;
                }                
            }
            return result;
        }
        
        public void End()
        {
            nodes = null;

            NumPoints = 0;
            NumFaces = 0;
            for (int i = 0; i < Partitions.Count; i++)
            {
                Partitions[i].End();
                NumPoints += Partitions[i].Vertices.Length;
                NumFaces += Partitions[i].Indices.Length / 3;
            }

            foreach (TexCoordPartition par in Partitions)
                par.InitNormals();
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
                offset += Partitions[i].Vertices.Length;
            }
            return result;
        }
    }
}
