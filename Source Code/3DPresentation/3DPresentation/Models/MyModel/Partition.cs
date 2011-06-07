using System;
using System.Net;
using System.Windows;
using System.Windows.Controls;
using System.Windows.Documents;
using System.Windows.Ink;
using System.Windows.Input;
using System.Windows.Media;
using System.Windows.Media.Animation;
using System.Windows.Shapes;
using System.Collections.Generic;
using System.Text;
using Microsoft.Xna.Framework;
using Microsoft.Xna.Framework.Graphics;

namespace _3DPresentation
{
    public class Partition
    {
        private double THRESHOLD = 30;

        
        private int PartitionWidth;
        private int PartitionHeight;
        private int PartitionRealWidth;
        private int PartitionRealHeight;

        delegate void TriangleHadler(object param, int triangleCount, int i1, int i2, int i3);
        public VertexPositionNormalColor[] Vertices;
        public VertexBuffer VertexBuffer;

        Dictionary<GlobalVars.LOD, IndexBuffer> IndexBuffers;
        public int Length
        {
            get { return Vertices.Length; }
        }

        #region SetUp
        public Partition(int partitionWidth, int partitionHeight, int partitionRealWidth, int partitionRealHeight)
        {
            PartitionWidth = partitionWidth;
            PartitionHeight = partitionHeight;

            PartitionRealWidth = partitionRealWidth;
            PartitionRealHeight = partitionRealHeight;

            Vertices = new VertexPositionNormalColor[PartitionRealWidth * PartitionRealHeight];
            IndexBuffers = new Dictionary<_3DPresentation.GlobalVars.LOD, IndexBuffer>();
        }

        public bool AddVertex(VertexPositionNormalColor vertex, int row, int col)
        {
            if (!(row < PartitionHeight && col < PartitionWidth))
                return false;
            Vertices[col + row * PartitionRealWidth] = vertex;
            return true;
        }

        public void InitBuffer(GraphicsDevice graphicsDevice)
        {
            VertexBuffer = new VertexBuffer(graphicsDevice, VertexPositionNormalColor.VertexDeclaration, Vertices.Length, BufferUsage.WriteOnly);
            VertexBuffer.SetData(0, Vertices, 0, Vertices.Length, 0);
        }
        #endregion

        #region Iterate Partition
        StringBuilder debugString = new StringBuilder();
        private int iterateThroughPartition(int step, object param, TriangleHadler triangleHandler)
        {
            int triangleCount = 0;
            for (int row = 0; row < PartitionRealHeight + step - 1; row += step)
            {
                for (int col = 0; col < PartitionRealWidth + step - 1; col += step)
                {
                    if (col >= PartitionRealWidth)
                        col = col;
                    try
                    {
                        if (((row / step) & 0x01) == 0)
                        {
                            if (((col / step) & 0x01) == 0)
                            {
                                FormTriangle(row, col, step, param, ref triangleCount, triangleHandler);
                            }
                        }
                        else if(((row / step) & 0x01) == 1)
                        {
                            if (((col / step) & 0x01) == 1)
                            {
                                FormTriangle(row, col, step, param, ref triangleCount, triangleHandler);
                            }
                        }
                    }
                    catch (Exception ex)
                    {
                        debugString.AppendFormat("row : {0}, col : {1} \n", row, col);
                    }
                }
            }

            return triangleCount;
        }

        private Vector2 index2Vertor(int index)
        {
            Vector2 v = new Vector2();
            v.X = index % PartitionRealWidth;
            v.Y = index / PartitionRealWidth;
            return v;
        }

        enum SpatialRelative {Top, Left, Right, Bot}
        private int GetGoodRelative(int row, int col, int step, SpatialRelative sr)
        {
            int r = 0; int c = 0;

            if (sr == SpatialRelative.Top)
            {
                r = (row - step) >= 0 ? (row - step) : 0;
                c = col < PartitionRealWidth ? col : PartitionRealWidth - 1;
            }
            else if (sr == SpatialRelative.Left)
            {
                r = row < PartitionRealHeight ? row : PartitionRealHeight - 1;
                c = (col - step) >= 0 ? (col - step) : 0;
            }
            else if (sr == SpatialRelative.Right)
            {
                r = row < PartitionRealHeight ? row : PartitionRealHeight - 1;
                c = (col + step) < PartitionRealWidth ? (col + step) : PartitionRealWidth - 1;
            }
            else if (sr == SpatialRelative.Bot)
            {
                r = (row + step) < PartitionRealHeight ? (row + step) : PartitionRealHeight - 1;
                c = col < PartitionRealWidth ? col : PartitionRealWidth - 1;
            }
            if (r * PartitionRealWidth + c > Vertices.Length)
                return -1;
            return r * PartitionRealWidth + c;
        }
        private void FormTriangle(int row, int col, int step, object param, ref int triangleCount, TriangleHadler triangleHandler)
        {
            int top, left, right, bot;
            int index = 0;

            top = GetGoodRelative(row, col, step, SpatialRelative.Top);
            left = GetGoodRelative(row, col, step, SpatialRelative.Left);
            right = GetGoodRelative(row, col, step, SpatialRelative.Right);
            bot = GetGoodRelative(row, col, step, SpatialRelative.Bot);

            // For vertex on the edge connect back to main grid
            row = row < PartitionRealHeight ? row : PartitionRealHeight - 1;
            col = col < PartitionRealWidth ? col : PartitionRealWidth - 1;
            index = row * PartitionRealWidth + col;

            
            // form 4 triangles : clockwise order
            if (index != top && index != right)
            {
                if (CheckDistance(index, top, right))
                {
                    triangleHandler(param, triangleCount++, index, top, right);
                }
            }
            if (index != right && index != bot)
            {
                if (CheckDistance(index, right, bot))
                {
                    triangleHandler(param, triangleCount++, index, right, bot);
                }
            }
            if (index != bot && index != left)
            {
                if (CheckDistance(index, bot, left))
                {
                    triangleHandler(param, triangleCount++, index, bot, left);
                }
            }
            if (index != left && index != top)
            {
                if (CheckDistance(index, left, top))
                {
                    triangleHandler(param, triangleCount++, index, left, top);
                }
            }
        }

        private bool CheckDistance(int i1, int i2, int i3)
        {
            //if (Math.Abs(Vertices[i1].Position.Z - Vertices[i2].Position.Z) > THRESHOLD)
            //    return false;
            //if (Math.Abs(Vertices[i1].Position.Z - Vertices[i3].Position.Z) > THRESHOLD)
            //    return false;
            //if (Math.Abs(Vertices[i2].Position.Z - Vertices[i3].Position.Z) > THRESHOLD)
            //    return false;

            //if (Vertices[i1].Position == Vertices[i2].Position
            //    || Vertices[i1].Position == Vertices[i3].Position
            //    || Vertices[i2].Position == Vertices[i3].Position)
            //    return false;

            if (Vector3.Distance(Vertices[i1].Position, Vertices[i2].Position) > THRESHOLD)
                return false;
            if (Vector3.Distance(Vertices[i1].Position, Vertices[i3].Position) > THRESHOLD)
                return false;
            return true;
        }
        #endregion        

        #region Indices
        public IndexBuffer GetIndexBuffer(_3DPresentation.GlobalVars.LOD lod, GraphicsDevice graphicsDevice)
        {
            IndexBuffer indexBuffer = null;
            ushort[] indices;
            int triangleCount;
            if (IndexBuffers.ContainsKey(lod))
            {
                indexBuffer =  IndexBuffers[lod];
            }
            else
            {
                // set Indices
                int step = (int)lod;
                indices = new ushort[PartitionWidth * PartitionHeight * 6];
                triangleCount = iterateThroughPartition(step, indices, AddTriangleToIndices);

                indexBuffer = new IndexBuffer(graphicsDevice, IndexElementSize.SixteenBits, triangleCount * 3, BufferUsage.WriteOnly);
                indexBuffer.SetData(0, indices, 0, triangleCount * 3);

                IndexBuffers.Add(lod, indexBuffer);
            }
            return indexBuffer;
        }
        void AddTriangleToIndices(object param, int triangleCount, int i1, int i2, int i3)
        {
            ushort[] indices = param as ushort[];
            if (indices != null)
            {
                try
                {
                    indices[triangleCount * 3] = (ushort)i1;
                    indices[triangleCount * 3 + 1] = (ushort)i2;
                    indices[triangleCount * 3 + 2] = (ushort)i3;
                }
                catch (Exception ex)
                {
                    debugString.AppendFormat("triangleCount : {0}, i1 : {1}, i2 : {2}, i3 : {3}", triangleCount, i1, i2, i3);
                }
            }
        }
        #endregion

        #region FillTheGap
        public enum GapType { RIGHT, BOT, RIGHT_BOT };
        public void FillTheGap(Partition target, GapType gapType)
        {
            if (gapType == GapType.BOT)
            {
                for (int i = 0; i < PartitionWidth; i++)
                {
                    Vertices[PartitionHeight * PartitionRealWidth + i] = target.Vertices[i];
                }
            }
            else if (gapType == GapType.RIGHT)
            {
                for (int i = 0; i < PartitionHeight; i++)
                {
                    Vertices[(i + 1) * PartitionRealWidth - 1] = target.Vertices[i * PartitionRealWidth];
                }
            }
            else if (gapType == GapType.RIGHT_BOT)
            {
                Vertices[PartitionRealWidth * PartitionRealHeight - 1] = target.Vertices[0];
            }
        }
        #endregion

        #region CalculateNormalVector
        public void CalculateNormalVector(GlobalVars.LOD lod)
        {
            int step = (int)lod;
            iterateThroughPartition(step, null, CalculateNormalVector_Phrase1);
            CalculateNormalVector_Phrase2();
        }

        void CalculateNormalVector_Phrase1(object param, int triangleCount, int i1, int i2, int i3)
        {
            Vector3 v1 = Vertices[i2].Position - Vertices[i1].Position;
            Vector3 v2 = Vertices[i3].Position - Vertices[i1].Position;
            Vector3 normal = Vector3.Cross(v2, v1);

            Vertices[i1].Normal += normal;
            Vertices[i2].Normal += normal;
            Vertices[i3].Normal += normal;
        }

        void CalculateNormalVector_Phrase2()
        {
            for (int i = 0; i < Vertices.Length; i++)
            {
                Vertices[i].Normal.Normalize();
            }
        }
        #endregion
    }
}
