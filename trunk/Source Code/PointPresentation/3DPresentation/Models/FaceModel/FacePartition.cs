﻿using System;
using System.Collections.Generic;
using Microsoft.Xna.Framework.Graphics;
using Microsoft.Xna.Framework;
using System.IO;


namespace _3DPresentation.Models
{
    public class FacePartition
    {
        public int ID;
        public List<VertexPositionNormalColor> VerticesList;        
        public List<ushort> IndicesList;

        public VertexPositionNormalColor[] Vertices;
        public ushort[] Indices;

        public int PartitionSize;
        private int Current;
        public VertexBuffer VertexBuffer;
        public IndexBuffer IndexBuffer;

        public bool IsValid
        {
            get;
            private set;
        }

        public FacePartition(int partitionSize, int id)
        {
            PartitionSize = partitionSize;
            ID = id;                     
        }

        public bool IsFull()
        {
            if (Current >= PartitionSize)
                return true;
            return false;
        }

        public void Begin()
        {
            VerticesList = new List<VertexPositionNormalColor>();
            IndicesList = new List<ushort>();
            Current = 0;
        }

        public void End()
        {
            Vertices = VerticesList.ToArray();
            // release the memory
            VerticesList.Clear(); 
            VerticesList = null;

            Indices = IndicesList.ToArray();
            IndicesList.Clear(); 
            IndicesList = null;
        }

        public int AddPoint(Vector3 point, Color color)
        {
            VerticesList.Add(new VertexPositionNormalColor(point, color, new Vector3(0, 0, 0)));
            return VerticesList.Count - 1;
        }

        public int AddPoint(Vector3 point, Vector3 normal, Color color)
        {
            VerticesList.Add(new VertexPositionNormalColor(point, color, normal));
            return VerticesList.Count - 1;
        }

        private int maxIndex = -1;
        private int maxI = -1;
        public bool AddIndice(int i1, int i2, int i3)
        {
            if (i1 >= this.VerticesList.Count || i2 >= this.VerticesList.Count || i3 >= this.VerticesList.Count)
                return false;

            IndicesList.Add(Convert.ToUInt16(i1));
            IndicesList.Add(Convert.ToUInt16(i2));
            IndicesList.Add(Convert.ToUInt16(i3));
            Current++;

            if (Convert.ToUInt16(i1) > maxIndex) { maxIndex = Convert.ToUInt16(i1); maxI = i1; }
            if (Convert.ToUInt16(i2) > maxIndex) { maxIndex = Convert.ToUInt16(i2); maxI = i2; }
            if (Convert.ToUInt16(i3) > maxIndex) { maxIndex = Convert.ToUInt16(i3); maxI = i3; }
            return true;
        }

        public void InitNormals()
        {
            // MUST USE VERTICES ARRAY
            // - VertexPositionNormalColor is a struct => VerticesList[i] : only return a copy of the actual Vertex in List
            //      => any modification'll only affect the copy, not the real one.            

            for (int i = 0; i < Indices.Length / 3; i++)
            {
                int i1 = Indices[i * 3];
                int i2 = Indices[i * 3 + 1];
                int i3 = Indices[i * 3 + 2];
                Vector3 v1 = Vertices[i3].Position - Vertices[i1].Position;
                Vector3 v2 = Vertices[i2].Position - Vertices[i1].Position;
                Vector3 normal = Vector3.Cross(v2, v1);

                Vertices[i1].Normal += normal;
                Vertices[i2].Normal += normal;
                Vertices[i3].Normal += normal;
            }

            for (int i = 0; i < Vertices.Length; i++)
            {
                Vertices[i].Normal.Normalize();
            }
        }

        public void InitBuffers(GraphicsDevice graphicsDevice)
        {
            if ((Vertices.Length == 0) || (Indices.Length < 3))
            {
                IsValid = false;
                return;
            }

            VertexBuffer = new VertexBuffer(graphicsDevice, VertexPositionNormalColor.VertexDeclaration, Vertices.Length, BufferUsage.WriteOnly);
            VertexBuffer.SetData(0, Vertices, 0, Vertices.Length, 0);
            
            IndexBuffer = new IndexBuffer(graphicsDevice, IndexElementSize.SixteenBits, Indices.Length, BufferUsage.WriteOnly);
            IndexBuffer.SetData(0, Indices, 0, Indices.Length);

            //Vertices = null;
            //Indices = null;
            IsValid = true;
        }

        public void Render(GraphicsDevice graphicsDevice)
        {
            if (IsValid == false)
                return;

            graphicsDevice.SetVertexBuffer(VertexBuffer);
            graphicsDevice.Indices = IndexBuffer;

            graphicsDevice.DrawIndexedPrimitives(PrimitiveType.TriangleList, 0, 0, VertexBuffer.VertexCount, 0, IndexBuffer.IndexCount / 3);
        }

        public bool ExportVertexData(BaseModel.FileType fileType, BaseModel.VertexTypes vertexType, StreamWriter writer, Matrix transformMatrix)
        {
            if (writer == null)
                return false;
            if (fileType == BaseModel.FileType.PLY)
            {
                if (vertexType == BaseModel.VertexTypes.XYZ)
                {
                    for (int i = 0; i < Vertices.Length; i++)
                    {
                        Vector3 worldPosition = MathUtil.TransformPoint(transformMatrix, Vertices[i].Position);
                        string str = string.Format("{0} {1} {2}\n", worldPosition.X, worldPosition.Y, worldPosition.Z);
                        writer.Write(str);
                    }
                }
                else if (vertexType == BaseModel.VertexTypes.XYZ_RGB)
                {
                    for (int i = 0; i < Vertices.Length; i++)
                    {
                        Vector3 worldPosition = MathUtil.TransformPoint(transformMatrix, Vertices[i].Position);
                        string str = string.Format("{0} {1} {2} {3} {4} {5}\n",
                            worldPosition.X, worldPosition.Y, worldPosition.Z, Vertices[i].Color.R, Vertices[i].Color.G, Vertices[i].Color.B);
                        writer.Write(str);
                    }
                }
                else if (vertexType == BaseModel.VertexTypes.XYZ_NORMAL)
                {
                    for (int i = 0; i < Vertices.Length; i++)
                    {
                        Vector3 worldPosition = MathUtil.TransformPoint(transformMatrix, Vertices[i].Position);
                        string str = string.Format("{0} {1} {2} {3} {4} {5}\n",
                            worldPosition.X, worldPosition.Y, worldPosition.Z, Vertices[i].Normal.X, Vertices[i].Normal.Y, Vertices[i].Normal.Z);
                        writer.Write(str);
                    }
                }
                else if (vertexType == BaseModel.VertexTypes.XYZ_NORNAL_RGB)
                {
                    for (int i = 0; i < Vertices.Length; i++)
                    {
                        Vector3 worldPosition = MathUtil.TransformPoint(transformMatrix, Vertices[i].Position);
                        string str = string.Format("{0} {1} {2} {3} {4} {5} {6} {7} {8}\n",
                            worldPosition.X, worldPosition.Y, worldPosition.Z, Vertices[i].Normal.X, Vertices[i].Normal.Y, Vertices[i].Normal.Z, Vertices[i].Color.R, Vertices[i].Color.G, Vertices[i].Color.B);
                        writer.Write(str);
                    }
                }
            }
            return true;
        }

        public bool ExportIndiceData(BaseModel.FileType fileType, BaseModel.VertexTypes vertexType, StreamWriter writer, Matrix worldMatrix, long offset)
        {
            if (writer == null)
                return false;

            if (fileType == BaseModel.FileType.PLY)
            {
                for (int i = 0; i < Indices.Length; i += 3)
                {
                    string str = string.Format("3 {0} {1} {2}\n", Indices[i] + offset, Indices[i + 1] + offset, Indices[i + 2] + offset);
                    writer.Write(str);
                }
            }
            return true;
        }

        public void projectToImagePlane(Matrix mat, int iWidth, int iHeight, int[,] zBuffer, System.Windows.Media.Imaging.WriteableBitmap bm, float k)
        {
            int iHalfWidth = iWidth / 2;
            int iHalfHeight = iHeight / 2;
            for (int i = 0; i < Vertices.Length; i += 4)
            {
                Vector3 p3d = Vertices[i].Position * k;
                Vector3 p2d = MathUtil.TransformPoint(mat, p3d);
                p2d.X += iHalfWidth;
                p2d.Y = iHalfHeight - p2d.Y;
                if (0 <= p2d.X && p2d.X < iWidth && 0 <= p2d.Y && p2d.Y < iHeight)
                {
                    if (zBuffer[(int)p2d.X, (int)p2d.Y] != 0 && p3d.Z > zBuffer[(int)p2d.X, (int)p2d.Y]) continue;

                    zBuffer[(int)p2d.X, (int)p2d.Y] = (int)p3d.Z;
                    System.Windows.Media.Color clr = new System.Windows.Media.Color();
                    clr.A = 255;
                    clr.R = Vertices[i].Color.R;
                    clr.G = Vertices[i].Color.G;
                    clr.B = Vertices[i].Color.B;
                    System.Windows.Media.Imaging.WriteableBitmapExtensions.SetPixel(bm, (int)p2d.X, (int)p2d.Y, clr);
                }
            }
        }
    }
}
