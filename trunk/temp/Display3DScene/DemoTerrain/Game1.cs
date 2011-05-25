using System;
using System.Collections.Generic;
using Microsoft.Xna.Framework;
using Microsoft.Xna.Framework.Audio;
using Microsoft.Xna.Framework.Content;
using Microsoft.Xna.Framework.GamerServices;
using Microsoft.Xna.Framework.Graphics;
using Microsoft.Xna.Framework.Input;
using Microsoft.Xna.Framework.Net;
using Microsoft.Xna.Framework.Storage;
using System.IO;
using SD = System.Drawing;
using System.Runtime.InteropServices;

namespace DemoTerrain
{
    public class Game1 : Microsoft.Xna.Framework.Game
    {
        GraphicsDeviceManager graphics;
        SpriteBatch spriteBatch;
        GraphicsDevice device;
        Effect effect;
        VertexPositionColor[] vertices;
        VertexDeclaration myVertexDeclaration;
        int[] indices;
        BasicEffect basicEffect;
        Matrix viewMatrix;
        Matrix projectionMatrix;

        SpriteFont spriteFont;

        private int terrainWidth;
        private int terrainHeight;
        private float[,] heightData;
        float angle = 0;
        public Game1()
        {
            graphics = new GraphicsDeviceManager(this);
            Content.RootDirectory = "Content";
        }

        protected override void Initialize()
        {
            graphics.PreferredBackBufferWidth = 800;
            graphics.PreferredBackBufferHeight = 600;
            graphics.IsFullScreen = false;
            graphics.ApplyChanges();
            Window.Title = "Riemer's XNA Tutorials -- Series 1";

            base.Initialize();
        }

        protected override void LoadContent()
        {
            device = graphics.GraphicsDevice;
            spriteBatch = new SpriteBatch(GraphicsDevice);

            effect = Content.Load<Effect>("effects");
//            ColorTexture = LoadFromFile(@"g:\HappyDay.jpg");
            InitValues();

            LoadHeightData("Depthmap.txt");
            basicEffect = new BasicEffect(device, null);
            spriteFont = Content.Load<SpriteFont>("Georgia");
            SetUpVertices();
            SetUpCamera();
            SetUpIndices();

            avertex = new VertexPositionColor[6];
            avertex[0] = new VertexPositionColor(new Vector3(-3000, 0, 0), Color.Red);
            avertex[1] = new VertexPositionColor(new Vector3(+3000, 0, 0), Color.White);

            avertex[2] = new VertexPositionColor(new Vector3(0, -3000, 0), Color.Green);
            avertex[3] = new VertexPositionColor(new Vector3(0, 3000, 0), Color.White);

            avertex[4] = new VertexPositionColor(new Vector3(0, 0, -3000), Color.Blue);
            avertex[5] = new VertexPositionColor(new Vector3(0, 0, 3000), Color.White);

        }

        float degH = 57.0f;
        float degV = 43.0f;

        float radH;
        float radV;
        float dOH;
        Texture2D ColorTexture;

        void    InitValues()
        {
            radH = MathHelper.ToRadians(degH);
            radV = MathHelper.ToRadians(degV);
            dOH = (float)(320.0f / Math.Tan(radH / 2)); 
            // dOH = 240.0f * Math.Tan (radV / 2);
        }
        

        Vector3 Calc3DPos(Vector3 input)
        {
            Vector3 val;
            val.Z = -input.Z;
            val.X = input.Z * (input.X) / dOH;
            val.Y = -input.Z * (input.Y) / dOH;
 /*
            val.Z = -input.Z;
            val.X = 0;
            val.Y = 0;
            if (input.X<0)
            {
                float t = (float)(Math.Atan(-input.X / dOH));
                val.X = (float)(-Math.Sin(t)*input.Z);
            }
            else
            {
                float t = (float)(Math.Atan(input.X / dOH));
                val.X = (float)(Math.Sin(t) * input.Z);
            }
            if (input.Y < 0)
            {
                float t = (float)(Math.Atan(-input.Y / dOH));
                val.Y = -(float)(-Math.Sin(t) * input.Z);
            }
            else
            {
                float t = (float)(Math.Atan(input.Y / dOH));
                val.Y = -(float)(Math.Sin(t) * input.Z);
            }  
			*/
            return val;
        }
        int[] idx;
        int count = 0;

        private void SetUpVertices()
        {
            vertices = new VertexPositionColor[terrainWidth * terrainHeight];
            //SD.Bitmap   bm = new SD.Bitmap("ColorImg.PNG");
            //for (int x = 0; x < terrainWidth; x++)
            //{
            //    for (int y = 0; y < terrainHeight; y++)
            //    {
            //        Vector3 temp;
            //        temp = new Vector3(x - 320, y - 240, heightData[x, y]);
            //        vertices[x + y * terrainWidth].Position = Calc3DPos(temp);
            //      //  float ff = 1-(heightData[x, y]-mm) / (MM-mm);
            //      //  vertices[x + y * terrainWidth].Color = Color.White;//new Color(ff, ff, ff);
            //        int xx = x + 0;
            //        if (xx > 639) xx =639;
            //        vertices[x + y * terrainWidth].Color = new Color(bm.GetPixel(xx, y).R, bm.GetPixel(xx, y).G, bm.GetPixel(xx, y).B);
            //    }
            //}

            string filePath = @"c:\Program Files (x86)\OpenNI\Samples\NiSimpleViewer\DepthFrame00000004.txt";
            string line;

            StreamReader file = new StreamReader(filePath);
            int i = 0;
            while ((line = file.ReadLine()) != null)
            {
                string[] strTemp = line.Split(' ');
                vertices[i].Position = new Vector3(int.Parse(strTemp[0]), int.Parse(strTemp[1]), int.Parse(strTemp[2]));
                vertices[i].Color = new Color(float.Parse(strTemp[3]) / 255.0f, float.Parse(strTemp[4]) / 255.0f, float.Parse(strTemp[5]) / 255.0f);

                i++;
            }
            file.Close();

            idx = new int[(terrainWidth-1)*(terrainHeight-1) * 24];
            count = 0;
            for (int x = 0; x < terrainWidth-1; x++)
            {
                for (int y = 0; y < terrainHeight-1; y++)
                {
                    if (x>0)
                        AddTriangle((x + 0) + (y + 0) * terrainWidth, (x - 1) + (y + 0) * terrainWidth, (x + 0) + (y + 1) * terrainWidth);

                    if ((y>0) && (x>0))
                        AddTriangle((x + 0) + (y + 0) * terrainWidth, (x - 0) + (y - 1) * terrainWidth, (x - 1) + (y + 0) * terrainWidth);

                    AddTriangle((x + 0) + (y + 0) * terrainWidth, (x - 0) + (y + 1) * terrainWidth, (x + 1) + (y + 0) * terrainWidth);

                    if (y>0)
                        AddTriangle((x + 0) + (y + 0) * terrainWidth, (x + 1) + (y + 0) * terrainWidth, (x + 0) + (y - 1) * terrainWidth);

                }
            }

            myVertexDeclaration = new VertexDeclaration(device, VertexPositionColor.VertexElements);
        }

        int Threshold = 30;
        private void AddTriangle(int i1, int i2, int i3)
        {

            if (Math.Abs(vertices[i1].Position.Z - vertices[i2].Position.Z)>Threshold)
                return;
            if (Math.Abs(vertices[i1].Position.Z - vertices[i3].Position.Z) > Threshold)
                return;
            if (Math.Abs(vertices[i2].Position.Z - vertices[i3].Position.Z) > Threshold)
                return;

            idx[count + 0] = i1;
            idx[count + 1] = i2;
            idx[count + 2] = i3;
            count += 3;
        }

        VertexPositionColor[] avertex;

        private void SetUpIndices()
        {
            indices = new int[(terrainWidth - 1) * (terrainHeight - 1) * 6];
            int counter = 0;
            for (int y = 0; y < terrainHeight - 1; y++)
            {
                for (int x = 0; x < terrainWidth - 1; x++)
                {
                    int lowerLeft = x + y * terrainWidth;
                    int lowerRight = (x + 1) + y * terrainWidth;
                    int topLeft = x + (y + 1) * terrainWidth;
                    int topRight = (x + 1) + (y + 1) * terrainWidth;

                    indices[counter++] = topLeft;
                    indices[counter++] = lowerRight;
                    indices[counter++] = lowerLeft;

                    indices[counter++] = topLeft;
                    indices[counter++] = topRight;
                    indices[counter++] = lowerRight;
                }
            }
 
        }

        Vector3 Pos = new Vector3(0,0,0);

        private void SetUpCamera()
        {
            viewMatrix = Matrix.CreateLookAt(Pos, new Vector3(0, 0, -1000), new Vector3(0, 1, 0));
            projectionMatrix = Matrix.CreatePerspectiveFieldOfView(MathHelper.PiOver4, device.Viewport.AspectRatio, 1.0f, 30000.0f);
        }


        Texture2D   LoadFromFile(string strFilename)
        {
            SD.Bitmap bitmap = new SD.Bitmap(strFilename);

            // Initialize our custom texture (should be defined in the class)
            Texture2D customTexture = new Texture2D(this.GraphicsDevice, bitmap.Width, bitmap.Height, 0, TextureUsage.None, SurfaceFormat.Color);

            // Lock the bitmap data
            SD.Imaging.BitmapData data = bitmap.LockBits(new System.Drawing.Rectangle(0, 0, bitmap.Width, bitmap.Height), System.Drawing.Imaging.ImageLockMode.ReadOnly, bitmap.PixelFormat);

            // calculate the byte size: for PixelFormat.Format32bppArgb (standard for GDI bitmaps) it's the hight * stride
            int bufferSize = data.Height * data.Stride; // stride already incorporates 4 bytes per pixel

            // create buffer
            byte[] bytes = new byte[bufferSize];

            // copy bitmap data into buffer
            Marshal.Copy(data.Scan0, bytes, 0, bytes.Length);

            // copy our buffer to the texture
            customTexture.SetData(bytes);

            // unlock the bitmap data
            bitmap.UnlockBits(data);
            return customTexture;
        }


        float MM;
        float mm;
        private void LoadHeightData(string s)
        {
            StreamReader sr = new StreamReader(s);

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
                    if (MM<heightData[x, y])
                        MM =heightData[x, y];
                    if (mm > heightData[x, y])
                        mm = heightData[x, y];
                }
            }
        }

        protected override void UnloadContent()
        {
        }

        protected override void Update(GameTime gameTime)
        {
            if (GamePad.GetState(PlayerIndex.One).Buttons.Back == ButtonState.Pressed)
                this.Exit();

            KeyboardState keyState = Keyboard.GetState();
            if (keyState.IsKeyDown(Keys.PageUp))
                angle += 0.05f;
            if (keyState.IsKeyDown(Keys.PageDown))
                angle -= 0.05f;

            if (keyState.IsKeyDown(Keys.A))
                Pos.X -= 10;;
            if (keyState.IsKeyDown(Keys.D))
                Pos.X += 10;;
            if (keyState.IsKeyDown(Keys.W))
                Pos.Y -= 10;;
            if (keyState.IsKeyDown(Keys.X))
                Pos.Y += 10;;
            if (keyState.IsKeyDown(Keys.Q))
                Pos.Z -= 10;;
            if (keyState.IsKeyDown(Keys.E))
                Pos.Z += 10;;
            viewMatrix = Matrix.CreateLookAt(Pos, new Vector3(0, 0,-1000), new Vector3(0, 1, 0));
            
            base.Update(gameTime);
        }

        protected override void Draw(GameTime gameTime)
        {
            device.Clear(Color.Black);
            device.RenderState.CullMode = CullMode.CullClockwiseFace;
            device.RenderState.FillMode = FillMode.Solid;

                        Matrix worldMatrix = Matrix.Identity;// Matrix.CreateRotationY(angle);

                /*        effect.CurrentTechnique = effect.Techniques["Colored"];
                        effect.Parameters["xView"].SetValue(viewMatrix);
                        effect.Parameters["xProjection"].SetValue(projectionMatrix);
                        effect.Parameters["xWorld"].SetValue(worldMatrix);
             effect.Begin();
                        foreach (EffectPass pass in effect.CurrentTechnique.Passes)
                        {
                            pass.Begin();

                            device.VertexDeclaration = myVertexDeclaration;

                            device.DrawUserPrimitives(PrimitiveType.PointList, vertices, 0, vertices.Length);
                            device.DrawUserPrimitives<VertexPositionColor>(
                 PrimitiveType.LineList, avertex, 0, 3);


                            pass.End();
                        }
                        effect.End();
             */
            basicEffect.VertexColorEnabled = true;
            basicEffect.World = worldMatrix;
            basicEffect.Projection= projectionMatrix;
            basicEffect.View = viewMatrix;

            basicEffect.Begin();
            foreach (EffectPass pass in basicEffect.CurrentTechnique.Passes)
            {
                pass.Begin();

                device.VertexDeclaration = myVertexDeclaration;

/*                device.DrawUserPrimitives(PrimitiveType.PointList, vertices, 0, vertices.Length);
                device.DrawUserPrimitives<VertexPositionColor>(
     PrimitiveType.LineList, avertex, 0, 3);*/

                device.DrawUserIndexedPrimitives(PrimitiveType.TriangleList, vertices, 0, vertices.Length, idx, 0, count/3);
                device.DrawUserPrimitives<VertexPositionColor>(
     PrimitiveType.LineList, avertex, 0, 3);

                pass.End();
            }
            basicEffect.End();
            

            spriteBatch.Begin();
            spriteBatch.DrawString(spriteFont, Pos.X.ToString() + " " + Pos.Y.ToString() +" "+ Pos.Z.ToString(), new Vector2(0,0), Color.White);
            spriteBatch.End();

            base.Draw(gameTime);
        }
    }
}