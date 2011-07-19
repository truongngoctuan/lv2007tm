using System;
using System.Collections.Generic;
using Microsoft.Xna.Framework;
using Microsoft.Xna.Framework.Graphics;
using System.IO;


namespace _3DPresentation.Models
{
    public class FaceManager
    {
        public class Node
        {
            public Vector3 Position;
            public Vector3 Normal;
            public Color Color;
            public int lastPartition;
            public int lastIndex;

            public Node(Vector3 position, Color color)
            {
                Position = position;
                Color = color;
                lastPartition = -1;
                lastIndex = -1;
            }
            public Node(Vector3 position, Vector3 normal, Color color)
            {
                Position = position;
                Normal = normal;
                Color = color;
                lastPartition = -1;
                lastIndex = -1;
            }
        }
        private Node[] Nodes;

        private static int PARTITION_BASE_SIZE = 2500;

        public List<FacePartition> Partitions;
        public int PartitionSize;
        public int NumPoints;
        public int NumFaces;

        BaseModel Model;
        public FaceManager(BaseModel model)
        {
            Partitions = new List<FacePartition>();
            Model = model;
        }

        public void Begin(int nPoints, int nFaces)
        {
            NumPoints = nPoints;
            NumFaces = nFaces;
            PartitionSize = PARTITION_BASE_SIZE < nFaces ? PARTITION_BASE_SIZE : nFaces;
            int nPartitions = (nFaces + PartitionSize - 1) / PartitionSize;
            for (int i = 0; i < nPartitions; i++)
            {
                Partitions.Add(new FacePartition(PartitionSize, i));
            }

            Nodes = new Node[nPoints];

            for (int i = 0; i < Partitions.Count; i++)
            {
                Partitions[i].Begin();
            }
        }

        int iCurrentNode = 0;
        public bool AddVertex(Vector3 position, Color color)
        {
            if (iCurrentNode >= Nodes.Length)
                return false;
            Nodes[iCurrentNode++] = new Node(position, color);
            return true;
        }
        public bool AddVertex(Vector3 position, Vector3 normal, Color color)
        {
            if (iCurrentNode >= Nodes.Length)
                return false;
            Nodes[iCurrentNode++] = new Node(position, normal, color);
            return true;
        }

        int iCurrentPartition = 0;
        public bool AddIndice(int i1, int i2, int i3)
        {
            if (i1 == i2 || i2 == i3 || i1 == i3)
                return false;
            bool result = false;
            while (iCurrentPartition < Partitions.Count)
            {
                FacePartition partition = Partitions[iCurrentPartition];
                if (partition.IsFull())
                {
                    iCurrentPartition++;
                }
                else
                {
                    if (Nodes[i1].lastPartition != Partitions[iCurrentPartition].ID)
                    {
                        Nodes[i1].lastPartition = partition.ID;
                        Nodes[i1].lastIndex = partition.AddPoint(Nodes[i1].Position, Nodes[i1].Normal, Nodes[i1].Color);
                    }
                    if (Nodes[i2].lastPartition != Partitions[iCurrentPartition].ID)
                    {
                        Nodes[i2].lastPartition = partition.ID;
                        Nodes[i2].lastIndex = partition.AddPoint(Nodes[i2].Position, Nodes[i2].Normal, Nodes[i2].Color);
                    }
                    if (Nodes[i3].lastPartition != Partitions[iCurrentPartition].ID)
                    {
                        Nodes[i3].lastPartition = partition.ID;
                        Nodes[i3].lastIndex = partition.AddPoint(Nodes[i3].Position, Nodes[i3].Normal, Nodes[i3].Color);
                    }
                    result = partition.AddIndice(Nodes[i1].lastIndex, Nodes[i2].lastIndex, Nodes[i3].lastIndex);
                    if (result)
                        break;
                }
            }
            return result;
        }        
        
        public void End()
        {
            Nodes = null;

            NumPoints = 0;
            NumFaces = 0;
            for (int i = 0; i < Partitions.Count; i++)
            {
                Partitions[i].End();
                NumPoints += Partitions[i].Vertices.Length;
                NumFaces += Partitions[i].Indices.Length / 3;
            }

            if (Model.Type == BaseModel.VertexTypes.XYZ_NORMAL_TEXCOORD
                || Model.Type == BaseModel.VertexTypes.XYZ_NORMAL
                || Model.Type == BaseModel.VertexTypes.XYZ_NORNAL_RGB)
                return;

            foreach (FacePartition par in Partitions)
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

        public void projectToImagePlane(Matrix mat, int iWidth, int iHeight, int[,] zBuffer, System.Windows.Media.Imaging.WriteableBitmap bm, float k)
        {
            for (int i = 0; i < Partitions.Count; i++)
            {
                Partitions[i].projectToImagePlane(mat, iWidth, iHeight, zBuffer, bm, k);
            }

        }
    }
}
