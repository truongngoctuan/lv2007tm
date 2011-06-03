using System;
using System.Net;
using System.Windows;
using Microsoft.Xna.Framework;
using Microsoft.Xna.Framework.Graphics;
using Microsoft.Xna.Framework.Silverlight;
using System.IO;
using System.Windows.Media.Imaging;
using Babylon.Toolbox;
using _3DPresentation.Effects.NoEffect;
using System.Windows.Threading;
using System.Collections.Generic;

namespace _3DPresentation
{
    /// <summary>
    /// Represents a vertex with position and color elements.
    /// </summary>
    public struct VertexPositionNormalColor
    {
        // MUST HAVE THE SAME ORDER as VertexDeclaration
        public Vector3 Position;
        public Vector3 Normal;        
        public Color Color;

        public VertexPositionNormalColor(Vector3 position, Color color, Vector3 normal)
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

    public struct VertexPositionColor
    {
        // MUST HAVE THE SAME ORDER as VertexDeclaration
        public Vector3 Position;
        public Color Color;

        public VertexPositionColor(Vector3 position, Color color)
        {
            Position = position;
            Color = color;
        }

        public static readonly VertexDeclaration VertexDeclaration = new VertexDeclaration(
            new VertexElement(0, VertexElementFormat.Vector3, VertexElementUsage.Position, 0),
            new VertexElement(sizeof(float) * 3, VertexElementFormat.Color, VertexElementUsage.Color, 0)
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
        VertexBuffer avertexBuffer;
        VertexBuffer lightSourceVertexBuffer;

        VertexPositionColor[] avertex;
        VertexPositionColor[] lightSourceVertices;

        public MeshManger meshManager;

        WriteableBitmap writeableBitmap;

        private int terrainWidth;
        private int terrainHeight;
        private float[,] heightData;

        
        NoEffect noEffect;
        BasicEffect basicEffect; private Texture2D texture;
        MyBasicEffect myBasicEffect;

        public SceneModel(bool solidFaceColor = true)
        {            
            Stream imageStream = Application.GetResourceStream(new Uri(@"3DPresentation;component/ColorImg.png", UriKind.Relative)).Stream;
            var bitmapImage = new BitmapImage();
            bitmapImage.SetSource(imageStream);
            writeableBitmap = new WriteableBitmap(bitmapImage);
            // Create texture           
            //texture = new Texture2D(resourceDevice, bitmapImage.PixelWidth, bitmapImage.PixelHeight, false, SurfaceFormat.Color);
            // Copy image to texture
            //bitmapImage.CopyTo(texture);

            // Initialize resources
            meshManager = new MeshManger();
            CreateModel();

            noEffect = new NoEffect(resourceDevice);
            myBasicEffect = new MyBasicEffect(resourceDevice);
            basicEffect = new BasicEffect(resourceDevice);            
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

            #region Axis
            avertex = new VertexPositionColor[6];
            avertex[0] = new VertexPositionColor(new Vector3(-3000, 0, 0), red);
            avertex[1] = new VertexPositionColor(new Vector3(+3000, 0, 0), Color.White);

            avertex[2] = new VertexPositionColor(new Vector3(0, -3000, 0), green);
            avertex[3] = new VertexPositionColor(new Vector3(0, 3000, 0), Color.White);

            avertex[4] = new VertexPositionColor(new Vector3(0, 0, -3000), blue);
            avertex[5] = new VertexPositionColor(new Vector3(0, 0, 3000), Color.White);

            avertexBuffer = new VertexBuffer(resourceDevice, VertexPositionColor.VertexDeclaration,
                avertex.Length, BufferUsage.WriteOnly);
            avertexBuffer.SetData(0, avertex, 0, avertex.Length, 0);
            #endregion

            #region LightSource
            lightSourceVertices = new VertexPositionColor[36];
            // face coordinates
            Vector3 topLeftFront = new Vector3(-10.0f, 10.0f, 10.0f);
            Vector3 bottomLeftFront = new Vector3(-10.0f, -10.0f, 10.0f);
            Vector3 topRightFront = new Vector3(10.0f, 10.0f, 10.0f);
            Vector3 bottomRightFront = new Vector3(10.0f, -10.0f, 10.0f);
            Vector3 topLeftBack = new Vector3(-10.0f, 10.0f, -10.0f);
            Vector3 topRightBack = new Vector3(10.0f, 10.0f, -10.0f);
            Vector3 bottomLeftBack = new Vector3(-10.0f, -10.0f, -10.0f);
            Vector3 bottomRightBack = new Vector3(10.0f, -10.0f, -10.0f);
            lightSourceVertices[0] = new VertexPositionColor(topRightFront, red);
            lightSourceVertices[1] = new VertexPositionColor(bottomLeftFront, orange);
            lightSourceVertices[2] = new VertexPositionColor(topLeftFront, yellow);
            lightSourceVertices[3] = new VertexPositionColor(topRightFront, red);
            lightSourceVertices[4] = new VertexPositionColor(bottomRightFront, green);
            lightSourceVertices[5] = new VertexPositionColor(bottomLeftFront, orange);

            // back face 
            lightSourceVertices[6] = new VertexPositionColor(bottomLeftBack, blue);
            lightSourceVertices[7] = new VertexPositionColor(topRightBack, purple);
            lightSourceVertices[8] = new VertexPositionColor(topLeftBack, black);
            lightSourceVertices[9] = new VertexPositionColor(bottomRightBack, cyan);
            lightSourceVertices[10] = new VertexPositionColor(topRightBack, purple);
            lightSourceVertices[11] = new VertexPositionColor(bottomLeftBack, blue);

            // top face
            lightSourceVertices[12] = new VertexPositionColor(topLeftBack, black);
            lightSourceVertices[13] = new VertexPositionColor(topRightBack, purple);
            lightSourceVertices[14] = new VertexPositionColor(topLeftFront, yellow);
            lightSourceVertices[15] = new VertexPositionColor(topRightBack, purple);
            lightSourceVertices[16] = new VertexPositionColor(topRightFront, red);
            lightSourceVertices[17] = new VertexPositionColor(topLeftFront, yellow);

            // bottom face 
            lightSourceVertices[18] = new VertexPositionColor(bottomRightBack, cyan);
            lightSourceVertices[19] = new VertexPositionColor(bottomLeftBack, blue);
            lightSourceVertices[20] = new VertexPositionColor(bottomLeftFront, orange);
            lightSourceVertices[21] = new VertexPositionColor(bottomRightFront, green);
            lightSourceVertices[22] = new VertexPositionColor(bottomRightBack, cyan);
            lightSourceVertices[23] = new VertexPositionColor(bottomLeftFront, orange);

            // left face
            lightSourceVertices[24] = new VertexPositionColor(bottomLeftFront, orange);
            lightSourceVertices[25] = new VertexPositionColor(bottomLeftBack, blue);
            lightSourceVertices[26] = new VertexPositionColor(topLeftFront, yellow);
            lightSourceVertices[27] = new VertexPositionColor(topLeftFront, yellow);
            lightSourceVertices[28] = new VertexPositionColor(bottomLeftBack, blue);
            lightSourceVertices[29] = new VertexPositionColor(topLeftBack, black);

            // right face 
            lightSourceVertices[30] = new VertexPositionColor(bottomRightBack, cyan);
            lightSourceVertices[31] = new VertexPositionColor(bottomRightFront, green);
            lightSourceVertices[32] = new VertexPositionColor(topRightFront, red);
            lightSourceVertices[33] = new VertexPositionColor(bottomRightBack, cyan);
            lightSourceVertices[34] = new VertexPositionColor(topRightFront, red);
            lightSourceVertices[35] = new VertexPositionColor(topRightBack, purple);

            lightSourceVertexBuffer = new VertexBuffer(resourceDevice, VertexPositionColor.VertexDeclaration,
                lightSourceVertices.Length, BufferUsage.WriteOnly);
            lightSourceVertexBuffer.SetData(0, lightSourceVertices, 0, lightSourceVertices.Length, 0);
            #endregion
            
        }
        
        Vector3 xLightSource = new Vector3(0, 0, 1000);
        float xLightIntensity = 5000.0f;
        Color xDisfuseColor = Color.FromNonPremultiplied(255, 255, 255, 255);
        float xAmbientIntensity = 0.2f;

        Vector4 xNoEffect = new Vector4(0.0f, 0, 0, 0);
        Color DiffuseColor = Color.White;
        Color AmbientColor = Color.White;

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

            terrainWidth = 640;
            terrainHeight = 480;

            Color[] heightMapColors = new Color[terrainWidth * terrainHeight];
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
        
        private void SetUpVertices()
        {            
            meshManager.Begin(terrainWidth, terrainHeight);
            for (int x = 0; x < terrainWidth; x++)
            {
                for (int y = 0; y < terrainHeight; y++)
                {
                    Vector3 temp;
                    temp = new Vector3(x - 320, y - 240, heightData[x, y]);

                    VertexPositionNormalColor vertex = new VertexPositionNormalColor();
                    vertex.Position = Calc3DPos(temp);
                    vertex.Color = getPixel(x + y * terrainWidth);
                    vertex.Normal = new Vector3(0, 0, 0);
                    meshManager.AddVertex(vertex, y, x);
                }                
            }
            meshManager.End();
            meshManager.InitVertexBuffer(resourceDevice);
            
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
            get { return xLightIntensity; }
            set { xLightIntensity = value; }
        }
        public float AmbientIntensity
        {
            get { return xAmbientIntensity; }
            set { xAmbientIntensity = value; }
        }

        public int FPS
        {
            get;
            set;
        }

        int _total_frames = 0;
        DateTime _lastFPS = DateTime.Now;
        public int MyBlock
        {
            get;
            set;
        }

        public void Draw(GraphicsDevice graphicsDevice, TimeSpan totalTime, Matrix view, Matrix projection, Vector3 cameraPosition)
        {
            _total_frames++;
            if ((DateTime.Now - _lastFPS).Seconds >= 1)
            {
                FPS = _total_frames;
                _total_frames = 0;
                _lastFPS = DateTime.Now;
            }

            graphicsDevice.RasterizerState = new RasterizerState{
                FillMode = FillMode.Solid,
                CullMode = CullMode.None
            };

            Matrix world = Matrix.Identity;         

            SetShaderEffect(ShaderEffect.MyBasicEffect, graphicsDevice, world, view, projection, cameraPosition);
            int block = MyBlock < meshManager.Partitions.Count ? MyBlock : meshManager.Partitions.Count;
            for (int partitionIndex = 0; partitionIndex < block; partitionIndex++)
            {
                meshManager.RenderPartition(graphicsDevice, partitionIndex);
            }
            
            // Draw axis
            graphicsDevice.SetVertexBuffer(avertexBuffer);
            SetShaderEffect(ShaderEffect.NoEffect, graphicsDevice, world, view, projection, cameraPosition);            
            graphicsDevice.DrawPrimitives(PrimitiveType.LineList, 0, 3);

            graphicsDevice.SetVertexBuffer(lightSourceVertexBuffer);
            Matrix lightSource = Matrix.CreateTranslation(xLightSource);
            SetShaderEffect(ShaderEffect.NoEffect, graphicsDevice, lightSource, view, projection, cameraPosition);            
            graphicsDevice.DrawPrimitives(PrimitiveType.TriangleList, 0, 12);
        }

        enum ShaderEffect { NoEffect, MyBasicEffect, BasicEffect };
        private void SetShaderEffect(ShaderEffect shaderEffect, GraphicsDevice graphicsDevice, Matrix world, Matrix view, Matrix projection, Vector3 cameraPosition)
        {
            if(shaderEffect == ShaderEffect.NoEffect)
            {
                noEffect.World = world;
                noEffect.Projection = projection;
                noEffect.View = view;

                noEffect.Device = graphicsDevice;
                noEffect.Apply();
            }
            else if (shaderEffect == ShaderEffect.MyBasicEffect)
            {
                myBasicEffect.World = world;
                myBasicEffect.Projection = projection;
                myBasicEffect.View = view;
                myBasicEffect.LightSource = xLightSource;
                myBasicEffect.LightIntensity = xLightIntensity;
                myBasicEffect.DiffuseColor = xDisfuseColor;
                myBasicEffect.AmbientIntensity = xAmbientIntensity;

                myBasicEffect.Device = graphicsDevice;
                myBasicEffect.Apply();
            }
            else if (shaderEffect == ShaderEffect.BasicEffect)
            {
                basicEffect.World = Matrix.Identity;
                basicEffect.View = view;
                basicEffect.Projection = projection;
                basicEffect.CameraPosition = cameraPosition;
                basicEffect.LightPosition = xLightSource;
                basicEffect.AmbientColor = DiffuseColor;
                basicEffect.DiffuseColor = AmbientColor;
                basicEffect.EmissiveColor = Color.Black;
                basicEffect.DiffuseTexture = texture;
                basicEffect.Device = graphicsDevice;
                basicEffect.Apply();
            }
        }
    }
}
