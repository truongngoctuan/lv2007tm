using System;
using System.Net;
using System.Windows;
using Microsoft.Xna.Framework;
using Microsoft.Xna.Framework.Graphics;
using Microsoft.Xna.Framework.Silverlight;
using System.IO;
using System.Windows.Media.Imaging;

namespace _3DPresentation
{
    /// <summary>
    /// Represents a vertex with position and color elements.
    /// </summary>
    public struct VertexPositionColor
    {
        public Vector3 Position;
        public Color Color;

        public VertexPositionColor(Vector3 position, Color color)
        {
            Position = position;
            Color = color;
        }

        public static readonly VertexDeclaration VertexDeclaration = new VertexDeclaration(
            new VertexElement(0, VertexElementFormat.Vector3, VertexElementUsage.Position, 0),
            new VertexElement(12, VertexElementFormat.Color, VertexElementUsage.Color, 0)
            );
    }

    /// <summary>
    /// Represents a Scene model made of multiple triangles.
    /// </summary>
    public class SceneModel
    {
        // the device to use when creating resources
        static readonly GraphicsDevice resourceDevice = GraphicsDeviceManager.Current.GraphicsDevice;

        bool bUseTriangle = false;

        // resources
        VertexBuffer vertexBuffer; VertexBuffer avertexBuffer;
        IndexBuffer indexBuffer;
        VertexShader vertexShader;
        PixelShader pixelShader;

        VertexPositionColor[] vertices; VertexPositionColor[] fullVertices;
        VertexPositionColor[] avertex;

        WriteableBitmap writeableBitmap;

        private int terrainWidth;
        private int terrainHeight;
        private float[,] heightData;

        public SceneModel(bool solidFaceColor = true)
        {
            Stream imageStream = Application.GetResourceStream(new Uri(@"3DPresentation;component/ColorImg.png", UriKind.Relative)).Stream;
            var bitmapImage = new BitmapImage();
            bitmapImage.SetSource(imageStream);
            writeableBitmap = new WriteableBitmap(bitmapImage);
            // Initialize resources required to draw the Cube
            CreateCube();

            Stream shaderStream = Application.GetResourceStream(new Uri(@"3DPresentation;component/Cube.vs", UriKind.Relative)).Stream;
            vertexShader = VertexShader.FromStream(resourceDevice, shaderStream);

            shaderStream = Application.GetResourceStream(new Uri(@"3DPresentation;component/Cube.ps", UriKind.Relative)).Stream;
            pixelShader = PixelShader.FromStream(resourceDevice, shaderStream);
        }

        /// <summary>
        /// Creates a vertex buffer that defines a cube
        /// </summary>
        /// <returns>A vertex buffer that defines a cube</returns>
        void CreateCube()
        {
            Stream stream = Application.GetResourceStream(new Uri(@"3DPresentation;component/depthmap.txt", UriKind.Relative)).Stream;
            LoadHeightData(stream);
            InitValues();
            SetUpVertices();

            Color red = Color.FromNonPremultiplied(255, 0, 0, 255);
            Color green = Color.FromNonPremultiplied(0, 255, 0, 255);
            Color blue = Color.FromNonPremultiplied(0, 0, 255, 255);
            Color orange = Color.FromNonPremultiplied(255, 128, 0, 255);
            Color yellow = Color.FromNonPremultiplied(255, 255, 0, 255);
            Color purple = Color.FromNonPremultiplied(128, 0, 255, 255);
            Color black = Color.FromNonPremultiplied(0, 0, 0, 255);
            Color cyan = Color.FromNonPremultiplied(0, 255, 255, 255);

            avertex = new VertexPositionColor[6];
            avertex[0] = new VertexPositionColor(new Vector3(-3000, 0, 0), red);
            avertex[1] = new VertexPositionColor(new Vector3(+3000, 0, 0), Color.White);

            avertex[2] = new VertexPositionColor(new Vector3(0, -3000, 0), green);
            avertex[3] = new VertexPositionColor(new Vector3(0, 3000, 0), Color.White);

            avertex[4] = new VertexPositionColor(new Vector3(0, 0, -3000), blue);
            avertex[5] = new VertexPositionColor(new Vector3(0, 0, 3000), Color.White);
            
            fullVertices = new VertexPositionColor[count];
            for (int i = 0; i < count; i++)
            {
                fullVertices[i].Position = vertices[idx[i]].Position;
                fullVertices[i].Color = vertices[idx[i]].Color;
            }

            vertexBuffer = new VertexBuffer(resourceDevice, VertexPositionColor.VertexDeclaration,
                fullVertices.Length, BufferUsage.WriteOnly);
            vertexBuffer.SetData(0, fullVertices, 0, fullVertices.Length, 0);

            avertexBuffer = new VertexBuffer(resourceDevice, VertexPositionColor.VertexDeclaration,
                avertex.Length, BufferUsage.WriteOnly);
            avertexBuffer.SetData(0, avertex, 0, avertex.Length, 0);
        }

        float degH = 57.0f;
        float degV = 43.0f;

        float radH;
        float radV;
        float dOH;
        void InitValues()
        {
            radH = MathHelper.ToRadians(degH);
            radV = MathHelper.ToRadians(degV);
            dOH = (float)(320.0f / Math.Tan(radH / 2));
        }


        Vector3 Calc3DPos(Vector3 input)
        {
            Vector3 val;
            val.Z = -input.Z;
            val.X = input.Z * (input.X) / dOH;
            val.Y = -input.Z * (input.Y) / dOH;

            return val;
        }

        float MM;
        float mm;
        private void LoadHeightData(Stream stream)
        {
            StreamReader sr = new StreamReader(stream);
            //StreamReader sr = new StreamReader(s);

            terrainWidth = 640;
            terrainHeight = 480;

            Color[] heightMapColors = new Color[terrainWidth * terrainHeight];

            //            heightMap.GetData(heightMapColors);
            //            sr.ReadLine();
            MM = 0;
            mm = 65000;
            heightData = new float[terrainWidth, terrainHeight];
            for (int y = 0; y < terrainHeight; y++)
            {
                string ss = sr.ReadLine();
                string[] Items = ss.Split(new char[] { '\t' });

                for (int x = 0; x < terrainWidth; x++)
                {
                    int t = Convert.ToInt32(Items[x]);
                    heightData[x, y] = t;
                    if (MM < heightData[x, y])
                        MM = heightData[x, y];
                    if (mm > heightData[x, y])
                        mm = heightData[x, y];
                }
            }
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

        int[] idx;
        int count = 0;
        private void SetUpVertices()
        {
            vertices = new VertexPositionColor[terrainWidth * terrainHeight];
            for (int x = 0; x < terrainWidth; x++)
            {
                for (int y = 0; y < terrainHeight; y++)
                {
                    Vector3 temp;
                    temp = new Vector3(x - 320, y - 240, heightData[x, y]);
                    vertices[x + y * terrainWidth].Position = Calc3DPos(temp);
                    int xx = x + 0;
                    if (xx > 639) 
                        xx = 639;
                    vertices[x + y * terrainWidth].Color = getPixel(x + y * terrainWidth);
                }                
            }

            idx = new int[(terrainWidth - 1) * (terrainHeight - 1) * 24];
            count = 0;
            for (int x = 0; x < terrainWidth - 1; x++)
            {
                for (int y = 0; y < terrainHeight - 1; y++)
                {
                    if (x > 0)
                        AddTriangle((x + 0) + (y + 0) * terrainWidth, (x - 1) + (y + 0) * terrainWidth, (x + 0) + (y + 1) * terrainWidth);

                    if ((y > 0) && (x > 0))
                        AddTriangle((x + 0) + (y + 0) * terrainWidth, (x - 0) + (y - 1) * terrainWidth, (x - 1) + (y + 0) * terrainWidth);

                    AddTriangle((x + 0) + (y + 0) * terrainWidth, (x - 0) + (y + 1) * terrainWidth, (x + 1) + (y + 0) * terrainWidth);

                    if (y > 0)
                        AddTriangle((x + 0) + (y + 0) * terrainWidth, (x + 1) + (y + 0) * terrainWidth, (x + 0) + (y - 1) * terrainWidth);
                }
            }
        }

        int Threshold = 30;
        private void AddTriangle(int i1, int i2, int i3)
        {
            if (Math.Abs(vertices[i1].Position.Z - vertices[i2].Position.Z) > Threshold)
                return;
            if (Math.Abs(vertices[i1].Position.Z - vertices[i3].Position.Z) > Threshold)
                return;
            if (Math.Abs(vertices[i2].Position.Z - vertices[i3].Position.Z) > Threshold)
                return;

            if (vertices[i1].Position == vertices[i2].Position
                || vertices[i1].Position == vertices[i3].Position
                || vertices[i2].Position == vertices[i3].Position)
                return;

            if (bUseTriangle)
            {
                #region use triangle
                idx[count + 0] = i1;
                idx[count + 1] = i2;
                idx[count + 2] = i3;
                count += 3;
                #endregion
            }
            else
            {
                #region use line
                idx[count + 0] = i1;
                idx[count + 1] = i2;
                count += 2;
                #endregion
            }
        }

        public void Draw(GraphicsDevice graphicsDevice, TimeSpan totalTime, Matrix viewProjection)
        {
            // update cube transform
            Matrix position = Matrix.Identity; // origin
            Matrix scale = Matrix.CreateScale(1.0f); // no scale modifier

            // create a continuously advancing rotation
            Matrix rotation = Matrix.CreateFromYawPitchRoll(
                MathHelper.PiOver4 * (float)totalTime.TotalSeconds,
                MathHelper.PiOver4 * (float)totalTime.TotalSeconds,
                0.0f);        
    
            // uncomment to stop rotation
            rotation = Matrix.Identity;

            // the world transform for the cube leaves it centered
            // at the origin but with the rotation applied
            Matrix world = Matrix.Identity;//scale * rotation * position;

            // calculate the final transform to pass to the shader
            Matrix worldViewProjection = world * viewProjection;

            // setup vertex pipeline
            graphicsDevice.SetVertexBuffer(vertexBuffer);
            //graphicsDevice.Indices = indexBuffer;

            graphicsDevice.SetVertexShader(vertexShader);
            graphicsDevice.SetVertexShaderConstantFloat4(0, ref worldViewProjection); // pass the transform to the shader

            // setup pixel pipeline
            graphicsDevice.SetPixelShader(pixelShader);

            // draw using the configured pipeline
            if (bUseTriangle)
            {
                #region use triangle
                int triangles = fullVertices.Length / 3;
                int trianglesPerDraw = 20000;
                int verticesPerDraw = trianglesPerDraw * 3;
                int n = triangles / trianglesPerDraw;
                for (int i = 0; i < n; i++)
                {
                    graphicsDevice.DrawPrimitives(PrimitiveType.TriangleList, i * verticesPerDraw, trianglesPerDraw);
                }
                #endregion
            }
            else
            {
                #region use lines
                int lines = fullVertices.Length / 2;
                int linesPerDraw = 20000;
                int verticesPerDraw = linesPerDraw * 2;
                int n = lines / linesPerDraw;
                for (int i = 0; i < n; i++)
                {
                    graphicsDevice.DrawPrimitives(PrimitiveType.LineList, i * verticesPerDraw, linesPerDraw);
                }
                #endregion
            }
        }
    }
}
