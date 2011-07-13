using System;
using System.Collections.Generic;
using Microsoft.Xna.Framework.Graphics;
using Microsoft.Xna.Framework;
using System.IO;


namespace _3DPresentation.Models
{
    public class PointPartition
    {
        private VertexPositionOffsetColor[] Vertices;
        private ushort[] Indices;
        public int PartitionSize;
        private int Current;
        public VertexBuffer VertexBuffer;
        public IndexBuffer IndexBuffer;

        public bool IsValid
        {
            get;
            private set;
        }

        public PointPartition(int partitionSize)
        {
            PartitionSize = partitionSize;
            Current = 0;                    
        }

        public void Begin()
        {
            Vertices = new VertexPositionOffsetColor[PartitionSize * 4];
            Indices = new ushort[PartitionSize * 6];
        }

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

        public void End()
        {
            ushort index = 0;
            for (int i = 0; i < Indices.Length; )
            {
                // clockwise triangle
                Indices[i++] = index++;
                Indices[i++] = index++;
                Indices[i++] = index--;

                // counter-clockwise triangle
                Indices[i++] = index++;
                Indices[i++] = index++;
                Indices[i++] = index++;
            }
        }

        public void InitBuffers(GraphicsDevice graphicsDevice)
        {
            if ((Vertices.Length == 0) || (Indices.Length < 3))
            {
                IsValid = false;
                return;
            }

            VertexBuffer = new VertexBuffer(graphicsDevice, VertexPositionOffsetColor.VertexDeclaration, Vertices.Length, BufferUsage.WriteOnly);
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

        public bool ExportVertexData(BaseModel.FileType fileType, BaseModel.VertexTypes vertexType, StreamWriter writer, Matrix worldMatrix)
        {
            if (writer == null)
                return false;
            if (fileType == BaseModel.FileType.PLY)
            {
                if (vertexType == BaseModel.VertexTypes.XYZ)
                {
                    for (int i = 0; i < Vertices.Length; i += 4)
                    {

                        Vector3 worldPosition = MathUtil.TransformPoint(worldMatrix, Vertices[i].Position);
                        if (worldPosition.X == worldPosition.Y && worldPosition.Y == worldPosition.Z && worldPosition.Z == 0) continue;

                        string str = string.Format("{0} {1} {2}\n",
                            worldPosition.X, worldPosition.Y, worldPosition.Z, Vertices[i].Color.R);
                        writer.Write(str);
                    }
                }
                else if (vertexType == BaseModel.VertexTypes.XYZ_RGB)
                {
                    for (int i = 0; i < Vertices.Length; i += 4)
                    {
                        Vector3 worldPosition = MathUtil.TransformPoint(worldMatrix, Vertices[i].Position);
                        if (worldPosition.X == worldPosition.Y && worldPosition.Y == worldPosition.Z && worldPosition.Z == 0) continue;

                        string str = string.Format("{0} {1} {2} {3} {4} {5}\n",
                            worldPosition.X, worldPosition.Y, worldPosition.Z, Vertices[i].Color.R, Vertices[i].Color.G, Vertices[i].Color.B);
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

            // point model doesn't have any face
            return true;
        }


        public void projectToImagePlane(Matrix mat, int iWidth, int iHeight, int[,] zBuffer, System.Windows.Media.Imaging.WriteableBitmap bm)
        {
            int iHalfWidth = iWidth / 2;
            int iHalfHeight = iHeight / 2;
            for (int i = 0; i < Vertices.Length; i += 4)
            {
                Vector3 p3d = Vertices[i].Position;
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
