
using _3DPresentation.Effects.MyBasicEffect;
using System.IO;
using Microsoft.Xna.Framework;
using Microsoft.Xna.Framework.Graphics;
using System.Windows;
using System;
using System.Windows.Media.Imaging;

namespace _3DPresentation.Models
{
    public class MyModel
    {
        public static string AssemblyName = "3DPresentation";
        public static float HORIZONTAL_ANGLE = 57.0f;
        public static float VERTICAL_ANGLE = 43.0f;

        public MeshManger meshManager;
        public int Width { get; set; }
        public int Height { get; set; }
        public bool IsInitialized { get; set; }

        private WriteableBitmap writeableBitmap;

        public string ImagePath { get; set; }
        public string DepthMapPath { get; set; }

        public float[,] heightData;
        float dOH;

        public Matrix WorldMatrix { get; set; }
        public bool IsVisible = true;
        public int NumberOfAcceptableVertices { get; set; }
        public MyModel(string imgPath, string depthmapPath, int width, int height)
        {
            ImagePath = imgPath;
            DepthMapPath = depthmapPath;
            Width = width;
            Height = height;
            WorldMatrix = Matrix.Identity;
        }
        
        public bool Init(GraphicsDevice graphicsDevice)
        {
            meshManager = new MeshManger();
            InitValues();
            LoadImage();
            LoadHeightData();
            SetupVertices(heightData, graphicsDevice);
            return true;
        }

        public Vector3 marker1 { get; set; }
        public Vector3 marker2 { get; set; }
        public Vector3 marker3 { get; set; }
        public void Render(GraphicsDevice graphicsDevice)
        {
            for (int partitionIndex = 0; partitionIndex < meshManager.Partitions.Count; partitionIndex++)
            //for (int partitionIndex = 0; partitionIndex < 7; partitionIndex++)
            {
                meshManager.RenderPartition(graphicsDevice, partitionIndex);
            }            
        }

        private void LoadImage()
        {
            Stream imageStream = Util.GetStream(AssemblyName, ImagePath);
            var bitmapImage = new BitmapImage();
            bitmapImage.SetSource(imageStream);
            writeableBitmap = new WriteableBitmap(bitmapImage);

            // Create texture           
            //texture = new Texture2D(resourceDevice, bitmapImage.PixelWidth, bitmapImage.PixelHeight, false, SurfaceFormat.Color);
            // Copy image to texture
            //bitmapImage.CopyTo(texture);
        }
        private void LoadHeightData()
        {
            Stream stream = Util.GetStream(AssemblyName, DepthMapPath);
            StreamReader sr = new StreamReader(stream);
            Width = 640;
            Height = 480;

            Color[] heightMapColors = new Color[Width * Height];
            heightData = new float[Width, Height];
            for (int y = 0; y < Height; y++)
            {
                string ss = sr.ReadLine();
                string[] Items = ss.Split(new char[] { '\t' });

                for (int x = 0; x < Width; x++)
                {
                    int t = Convert.ToInt32(Items[x]);
                    heightData[x, y] = t;
                }
            }
        }
        
        VertexPositionNormalColor[,] vertices; // test with export_pcd2
        private void SetupVertices(float[,] heightData, GraphicsDevice graphicsDevice) 
        {
            vertices = new VertexPositionNormalColor[Height, Width];
            NumberOfAcceptableVertices = 0;
            meshManager.Begin(Width, Height);
            for (int x = 0; x < Width; x++)
            {
                for (int y = 0; y < Height; y++)
                {
                    VertexPositionNormalColor vertex = new VertexPositionNormalColor();
                    vertex.Position = PixelToPoint(x, y);
                    vertex.Color = getPixel(x + y * Width);
                    vertex.Normal = new Vector3(0, 0, 0);                    
                    meshManager.AddVertex(vertex, y, x);

                    vertices[y, x] = vertex;
                    if (vertex.Position != Vector3.Zero)
                        ++NumberOfAcceptableVertices;
                }
            }
            meshManager.End();
            meshManager.InitVertexBuffer(graphicsDevice);
        }
        public Vector3 PixelToPoint(int x, int y)
        {
            Vector3 point;
            point = new Vector3(x - 320, y - 240, heightData[x, y]);
            point = Calc3DPos(point);
            return point;
        }
        
        private void InitValues()
        {
            float radH = MathHelper.ToRadians(HORIZONTAL_ANGLE);
            float radV = MathHelper.ToRadians(VERTICAL_ANGLE);
            dOH = (float)(320.0f / Math.Tan(radH / 2));
        }
        private Vector3 Calc3DPos(Vector3 input)
        {
            Vector3 val;
            val.Z = -input.Z;
            val.X = input.Z * (input.X) / dOH;
            val.Y = -input.Z * (input.Y) / dOH;

            return val;
        }
        private Color getPixel(int num)
        {
            int colorAsInt = writeableBitmap.Pixels[num];
            return Color.FromNonPremultiplied(
                                        (byte)((colorAsInt >> 16) & 0xff),
                                        (byte)((colorAsInt >> 8) & 0xff),
                                        (byte)((colorAsInt >> 0) & 0xff),
                                        (byte)((colorAsInt >> 24) & 0xff));
        }

        public void ExportMesh_PLY(StreamWriter sw)
        {
            if (sw == null)
                return;
            meshManager.Export_PLY(sw, this.WorldMatrix);
        }

        // Export to ply format
        public bool ExportMesh_PLY(FileInfo outFile)
        {
            bool bResult = true;
            try
            {
                Partition.ExportType = Partition.VertexExportType.PositionColor;

                StreamWriter sw = new StreamWriter(outFile.OpenWrite());                
                long NumberOfAcceptableVertices = this.NumberOfAcceptableVertices;

                if (Partition.ExportType == Partition.VertexExportType.Position)
                {
                    sw.WriteLine("ply");
                    sw.WriteLine("format ascii 1.0");
                    sw.WriteLine("element vertex " + NumberOfAcceptableVertices);
                    sw.WriteLine("property float32 x");
                    sw.WriteLine("property float32 y");
                    sw.WriteLine("property float32 z");
                    sw.WriteLine("end_header");
                }
                else if (Partition.ExportType == Partition.VertexExportType.PositionColor)
                {
                    sw.WriteLine("ply");
                    sw.WriteLine("format ascii 1.0");
                    sw.WriteLine("element vertex " + NumberOfAcceptableVertices);
                    sw.WriteLine("property float32 x");
                    sw.WriteLine("property float32 y");
                    sw.WriteLine("property float32 z");
                    sw.WriteLine("property uchar red");
                    sw.WriteLine("property uchar green");
                    sw.WriteLine("property uchar blue");
                    sw.WriteLine("end_header");
                }
                else if (Partition.ExportType == Partition.VertexExportType.PositionColorNormal)
                {
                    sw.WriteLine("ply");
                    sw.WriteLine("format ascii 1.0");
                    sw.WriteLine("element vertex " + NumberOfAcceptableVertices);
                    sw.WriteLine("property float32 x");
                    sw.WriteLine("property float32 y");
                    sw.WriteLine("property float32 z");
                    sw.WriteLine("property uchar red");
                    sw.WriteLine("property uchar green");
                    sw.WriteLine("property uchar blue");
                    sw.WriteLine("property float32 nx");
                    sw.WriteLine("property float32 ny");
                    sw.WriteLine("property float32 nz");
                    sw.WriteLine("end_header");
                }
                this.ExportMesh_PLY(sw);
                sw.Close();
            }
            catch (Exception ex)
            {
                bResult = false;
            }
            return bResult;
        }

        public void ExportMesh_PCD(StreamWriter sw)
        {
            if (sw == null)
                return;
            meshManager.Export_PCD(sw, this.WorldMatrix);
        }

        // Export to pcd format
        public bool ExportMesh_PCD(FileInfo outFile)
        {
            bool bResult = true;
            try
            {
                Partition.ExportType = Partition.VertexExportType.PositionColor;

                StreamWriter sw = new StreamWriter(outFile.OpenWrite());
                long NumberOfAcceptableVertices = this.NumberOfAcceptableVertices;

                if (Partition.ExportType == Partition.VertexExportType.Position)
                {
                    sw.WriteLine("# .PCD v.7 - Point Cloud Data file format");
                    sw.WriteLine("VERSION .7");
                    sw.WriteLine("FIELDS x y z");
                    sw.WriteLine("SIZE 4 4 4");
                    sw.WriteLine("TYPE F F F");
                    sw.WriteLine("COUNT 1 1 1");
                    sw.WriteLine("WIDTH " + NumberOfAcceptableVertices);
                    sw.WriteLine("HEIGHT 1");
                    sw.WriteLine("POINTS " + NumberOfAcceptableVertices);
                    sw.WriteLine("DATA ascii");
                }
                else if (Partition.ExportType == Partition.VertexExportType.PositionColor)
                {
                    sw.WriteLine("# .PCD v.7 - Point Cloud Data file format");
                    sw.WriteLine("VERSION .7");
                    sw.WriteLine("FIELDS x y z rgb");
                    sw.WriteLine("SIZE 4 4 4 4");
                    sw.WriteLine("TYPE F F F F");
                    sw.WriteLine("COUNT 1 1 1 1");
                    sw.WriteLine("WIDTH " + NumberOfAcceptableVertices);
                    sw.WriteLine("HEIGHT 1");
                    sw.WriteLine("POINTS " + NumberOfAcceptableVertices);
                    sw.WriteLine("DATA ascii");
                }
                else if (Partition.ExportType == Partition.VertexExportType.PositionColorNormal)
                {
                    sw.Close();
                    return false;
                }
                this.ExportMesh_PCD(sw);
                sw.Close();
            }
            catch (Exception ex)
            {
                bResult = false;
            }
            return bResult;
        }

        public bool ExportMesh_PCD2(FileInfo outFile)
        {
            bool bResult = true;
            try
            {
                Partition.ExportType = Partition.VertexExportType.PositionColor;

                StreamWriter sw = new StreamWriter(outFile.OpenWrite());
                long NumberOfAcceptableVertices = this.NumberOfAcceptableVertices;

                if (Partition.ExportType == Partition.VertexExportType.Position)
                {
                    sw.WriteLine("# .PCD v.7 - Point Cloud Data file format");
                    sw.WriteLine("VERSION .7");
                    sw.WriteLine("FIELDS x y z");
                    sw.WriteLine("SIZE 4 4 4");
                    sw.WriteLine("TYPE F F F");
                    sw.WriteLine("COUNT 1 1 1");
                    sw.WriteLine("WIDTH " + Width);
                    sw.WriteLine("HEIGHT " + Height);
                    sw.WriteLine("POINTS " + Width * Height);
                    sw.WriteLine("DATA ascii");
                }
                else if (Partition.ExportType == Partition.VertexExportType.PositionColor)
                {
                    sw.WriteLine("# .PCD v.7 - Point Cloud Data file format");
                    sw.WriteLine("VERSION .7");
                    sw.WriteLine("FIELDS x y z rgb");
                    sw.WriteLine("SIZE 4 4 4 4");
                    sw.WriteLine("TYPE F F F F");
                    sw.WriteLine("COUNT 1 1 1 1");
                    sw.WriteLine("WIDTH " + Width);
                    sw.WriteLine("HEIGHT " + Height);
                    sw.WriteLine("POINTS " + Width * Height);
                    sw.WriteLine("DATA ascii");
                }
                else if (Partition.ExportType == Partition.VertexExportType.PositionColorNormal)
                {
                    sw.Close();
                    return false;
                }
                foreach (VertexPositionNormalColor vertex in vertices)
                {
                    if (vertex.Position == Vector3.Zero)
                    {
                        sw.Write("nan nan nan");
                        sw.Write(' ');
                    }
                    else
                    {
                        Vector3 worldPosition = Util.TransformPoint(WorldMatrix, vertex.Position);
                        sw.Write(worldPosition.X);
                        sw.Write(' ');
                        sw.Write(worldPosition.Y);
                        sw.Write(' ');
                        sw.Write(worldPosition.Z);
                        sw.Write(' ');
                    }
                    int color = 0;
                    color = (vertex.Color.R << 16) | (vertex.Color.G << 8) | (vertex.Color.B << 0);
                    sw.Write(color);
                    sw.Write(' ');
                    sw.Write('\n');
                }

                sw.Close();
            }
            catch (Exception ex)
            {
                bResult = false;
            }
            return bResult;
        }
    }
}
