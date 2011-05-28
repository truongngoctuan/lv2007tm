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
        // MUST HAVE THE SAME ORDER as VertexDeclaration
        public Vector3 Position;
        public Vector3 Normal;        
        public Color Color;

        public VertexPositionColor(Vector3 position, Color color, Vector3 normal)
        {
            Position = position;
            Normal = normal;
            Color = color;
        }

        public static readonly VertexDeclaration VertexDeclaration = new VertexDeclaration(
            new VertexElement(0, VertexElementFormat.Vector3, VertexElementUsage.Position, 0),
            new VertexElement(sizeof(float) * 3, VertexElementFormat.Vector3, VertexElementUsage.Normal, 0),
            new VertexElement(sizeof(float) * (3 + 3), VertexElementFormat.Color, VertexElementUsage.Color, 0)            
            );
    }

    /// <summary>
    /// Represents a Scene model made of multiple triangles.
    /// </summary>
    public class SceneModel
    {
        // the device to use when creating resources
        static readonly GraphicsDevice resourceDevice = GraphicsDeviceManager.Current.GraphicsDevice;

        bool bUseTriangle = true;

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
            CreateModel();

            Stream shaderStream = Application.GetResourceStream(new Uri(@"3DPresentation;component/BasicVertexShader.vs", UriKind.Relative)).Stream;
            vertexShader = VertexShader.FromStream(resourceDevice, shaderStream);

            shaderStream = Application.GetResourceStream(new Uri(@"3DPresentation;component/BasicPixelShader.ps", UriKind.Relative)).Stream;
            pixelShader = PixelShader.FromStream(resourceDevice, shaderStream);
        }

        /// <summary>
        /// Creates a vertex buffer that defines a cube
        /// </summary>
        /// <returns>A vertex buffer that defines a cube</returns>
        void CreateModel()
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

            avertex = new VertexPositionColor[3];
            //avertex[0] = new VertexPositionColor(new Vector3(-3000, 0, 0), red, Vector3.Up);
            //avertex[1] = new VertexPositionColor(new Vector3(+3000, 0, 0), Color.White, Vector3.Up);

            //avertex[2] = new VertexPositionColor(new Vector3(0, -3000, 0), green, Vector3.Up);
            //avertex[3] = new VertexPositionColor(new Vector3(0, 3000, 0), Color.White, Vector3.Up);

            //avertex[4] = new VertexPositionColor(new Vector3(0, 0, -3000), blue, Vector3.Up);
            //avertex[5] = new VertexPositionColor(new Vector3(0, 0, 3000), Color.White, Vector3.Up);

            avertex[0] = new VertexPositionColor(new Vector3(-10, 0, -10), red, new Vector3(0, 0, 1));
            avertex[1] = new VertexPositionColor(new Vector3(10, 0, -10), green, new Vector3(0, 0, 1));
            avertex[2] = new VertexPositionColor(new Vector3(0, 10, -10), blue, new Vector3(0, 0, 1));
            
            //avertex[3] = new VertexPositionColor(new Vector3(0, 0, 0), Color.White, new Vector3(-1, 0, 2));

            //avertex[4] = new VertexPositionColor(new Vector3(-3, -5, -20), blue, new Vector3(-1, 0, 2));
            //avertex[5] = new VertexPositionColor(new Vector3(-3, 5, -25), Color.White, new Vector3(-1, 0, 2));

            fullVertices = new VertexPositionColor[count];
            for (int i = 0; i < count - 2; i += 3)
            {
                fullVertices[i].Position = vertices[idx[i]].Position;
                fullVertices[i].Color = vertices[idx[i]].Color;

                fullVertices[i+1].Position = vertices[idx[i+1]].Position;
                fullVertices[i+1].Color = vertices[idx[i+1]].Color;

                fullVertices[i+2].Position = vertices[idx[i+2]].Position;
                fullVertices[i+2].Color = vertices[idx[i+2]].Color;

                Vector3 v1 = fullVertices[i+1].Position - fullVertices[i].Position;
                Vector3 v2 = fullVertices[i+2].Position - fullVertices[i].Position;
                Vector3 normal = Vector3.Cross(v1, v2);
                //normal = new Vector3(0, 0, 1);
                fullVertices[i].Normal = normal;
                fullVertices[i+1].Normal = normal;
                fullVertices[i+2].Normal = normal;
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
                    vertices[x + y * terrainWidth].Color = getPixel(x + y * terrainWidth);
                    //vertices[x + y * terrainWidth].Normal = new Vector3(0, 0, 1);
                }                
            }

            idx = new int[(terrainWidth - 1) * (terrainHeight - 1) * 24];
            count = 0;
            int step = 1; //fineness : do min
            for (int x = 0; x < terrainWidth - step; x += step)
            {
                for (int y = 0; y < terrainHeight - step; y += step)
                {
                    if (x > step - 1)
                        AddTriangle((x + 0) + (y + 0) * terrainWidth, (x - step) + (y + 0) * terrainWidth, (x + 0) + (y + step) * terrainWidth);

                    if ((y > step - 1) && (x > step - 1))
                        AddTriangle((x + 0) + (y + 0) * terrainWidth, (x - 0) + (y - step) * terrainWidth, (x - step) + (y + 0) * terrainWidth);

                    AddTriangle((x + 0) + (y + 0) * terrainWidth, (x - 0) + (y + step) * terrainWidth, (x + step) + (y + 0) * terrainWidth);

                    if (y > step - 1)
                        AddTriangle((x + 0) + (y + 0) * terrainWidth, (x + step) + (y + 0) * terrainWidth, (x + 0) + (y - step) * terrainWidth);
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

        public float LightSourceX
        {
            get { return xLightSource.X; }
            set { xLightSource.X = value; }
        }
        public float LightSourceY
        {
            get { return xLightSource.Y; }
            set { xLightSource.Y = value; }
        }
        public float LightSourceZ
        {
            get { return xLightSource.Z; }
            set { xLightSource.Z = value; }
        }
        public float LightIntensity
        {
            get { return xLightIntensity.X; }
            set { xLightIntensity.X = value; }
        }
        public float AmbientIntensity
        {
            get { return xAmbientIntensity.X; }
            set { xAmbientIntensity.X = value; }
        }

        Vector4 xLightSource = new Vector4(0, 0, 1000, 0);
        Vector4 xLightIntensity = new Vector4(5000, 0, 0, 0);
        Vector4 xDisfuseColor = new Vector4(1.0f, 1.0f, 1.0f, 1.0f);
        Vector4 xAmbientIntensity = new Vector4(0.2f, 0, 0, 0);

        public void Draw(GraphicsDevice graphicsDevice, TimeSpan totalTime, Matrix viewProjection)
        {
            graphicsDevice.RasterizerState = new RasterizerState{
                FillMode = FillMode.Solid,
                CullMode = CullMode.CullClockwiseFace
            };
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
            graphicsDevice.SetVertexShaderConstantFloat4(4, ref world); // pass the transform to the shader
            // setup pixel pipeline            
            graphicsDevice.SetPixelShader(pixelShader);
            graphicsDevice.SetPixelShaderConstantFloat4(0, ref xLightSource);
            graphicsDevice.SetPixelShaderConstantFloat4(1, ref xLightIntensity);
            graphicsDevice.SetPixelShaderConstantFloat4(2, ref xDisfuseColor);
            graphicsDevice.SetPixelShaderConstantFloat4(3, ref xAmbientIntensity);
            //graphicsDevice.DrawPrimitives(PrimitiveType.TriangleList, 0, 1);

            //return;
            // draw using the configured pipeline
            if (bUseTriangle)
            {
                #region use triangle
                int triangles = fullVertices.Length / 3;
                int trianglesPerDraw = (triangles > 20000) ? 20000 : triangles;
                int verticesPerDraw = trianglesPerDraw * 3;
                int n = triangles / trianglesPerDraw;
                for (int i = 0; i < n; i++)
                {
                    graphicsDevice.DrawPrimitives(PrimitiveType.TriangleList, i * verticesPerDraw, trianglesPerDraw);
                }
                
                if(triangles - n * verticesPerDraw > 0)
                    graphicsDevice.DrawPrimitives(PrimitiveType.TriangleList, n * verticesPerDraw, triangles - n * verticesPerDraw);
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
