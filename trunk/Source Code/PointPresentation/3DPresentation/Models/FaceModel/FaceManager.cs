using System;
using System.Collections.Generic;
using Microsoft.Xna.Framework;
using Microsoft.Xna.Framework.Graphics;
using System.IO;


namespace _3DPresentation.Models
{
    public class FaceManager
    {
        public struct RelativeNode
        {
            public Node node2;
            public Node node3;
            public RelativeNode(Node n2, Node n3)
            {
                node2 = n2;
                node3 = n3;
            }
        }
        public class Node
        {
            public Vector3 Position;
            public Color Color;
            public List<RelativeNode> RelativeNodes;
            public int lastPartition;
            public int lastIndex;

            public Node(Vector3 position, Color color)
            {
                Position = position;
                Color = color;
                RelativeNodes = new List<RelativeNode>();
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
        
        public FaceManager()
        {
            Partitions = new List<FacePartition>();
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
        public bool AddIndice(int i1, int i2, int i3)
        {
            if (i1 == i2 || i2 == i3 || i1 == i3)
                return false;

            //if (i1 > i2) { int temp = i1; i1 = i2; i2 = temp; }
            //if (i1 > i3) { int temp = i1; i1 = i3; i3 = temp; }
            Nodes[i1].RelativeNodes.Add(new RelativeNode(Nodes[i2], Nodes[i3]));
            return true;
        }        
        
        public void End()
        {
            int iCurrentPartition = 0;
            FacePartition partition = Partitions[iCurrentPartition];
            for (int i = 0; i < Nodes.Length && iCurrentPartition < Partitions.Count; )
            {
                if (AddNode(Partitions[iCurrentPartition], Nodes[i]) == true)
                    i++;
                else
                    iCurrentPartition++;
            }
            Nodes = null;

            NumPoints = 0;
            NumFaces = 0;
            for (int i = 0; i < Partitions.Count; i++)
            {
                Partitions[i].End();
                NumPoints += Partitions[i].Vertices.Length;
                NumFaces += Partitions[i].Indices.Length / 3;
            }

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

        private bool AddNode(FacePartition partition, Node node)
        {
            if (partition.IsFull())
                return false;

            if (node.RelativeNodes.Count == 0)
                return true;

            if (node.lastPartition != partition.ID)
            {
                node.lastPartition = partition.ID;
                node.lastIndex = partition.AddPoint(node.Position, node.Color);
            }

            foreach (FaceManager.RelativeNode relative in node.RelativeNodes)
            {
                if (partition.IsFull())
                    return false;
                if (relative.node2.lastPartition != partition.ID)
                {
                    relative.node2.lastPartition = partition.ID;
                    relative.node2.lastIndex = partition.AddPoint(relative.node2.Position, relative.node2.Color);
                }
                if (relative.node3.lastPartition != partition.ID)
                {
                    relative.node3.lastPartition = partition.ID;
                    relative.node3.lastIndex = partition.AddPoint(relative.node3.Position, relative.node3.Color);
                }

                partition.AddIndice(node.lastIndex, relative.node2.lastIndex, relative.node3.lastIndex);
            }
            return true;
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

        public void projectToImagePlane(Matrix mat, int iWidth, int iHeight, int[,] zBuffer, System.Windows.Media.Imaging.WriteableBitmap bm)
        {
            for (int i = 0; i < Partitions.Count; i++)
            {
                Partitions[i].projectToImagePlane(mat, iWidth, iHeight, zBuffer, bm);
            }

        }
    }
}
