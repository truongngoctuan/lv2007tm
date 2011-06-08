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
using _3DPresentation.Effects.MyBasicEffect;
using _3DPresentation.Models;

namespace _3DPresentation
{
    /// <summary>
    /// Represents a Scene model made of multiple triangles.
    /// </summary>
    public class SceneModel
    {
        // the device to use when creating resources
        static readonly GraphicsDevice resourceDevice = GraphicsDeviceManager.Current.GraphicsDevice;

        // resources        
        NoEffect noEffect;
        BasicEffect basicEffect;
        MyBasicEffect myBasicEffect;
        
        List<MyModel> myModels;
        List<SimpleModel> simpleModels;
        List<LightPoint> lightPoints;

        public SceneModel(bool solidFaceColor = true)
        {
            myModels = new List<MyModel>();
            simpleModels = new List<SimpleModel>();
            lightPoints = new List<LightPoint>();

            noEffect = new NoEffect(resourceDevice);
            myBasicEffect = new MyBasicEffect(resourceDevice);
            basicEffect = new BasicEffect(resourceDevice);

            AmbientIntensity = 0.2f;
            LightIntensity = 5000.0f;
        }

        public MyModel AddMyModel(string imagePath, string depthmapPath, Vector3 position)
        {
            MyModel myModel = new MyModel(imagePath, depthmapPath, 640, 480);
            myModel.WorldMatrix = Matrix.CreateTranslation(position);
            myModel.Init(resourceDevice);
            myModels.Add(myModel);
            return myModel;
        }
        public SimpleModel AddSimpleModel(VertexPositionColor[] vertices, Vector3 position)
        {
            SimpleModel simpleModel = SimpleModel.CreateModel(resourceDevice, vertices);
            simpleModel.WorldMatrix = Matrix.CreateTranslation(position);
            simpleModel.RenderType = SimpleModel.Type.LineList;
            simpleModels.Add(simpleModel);
            return simpleModel;
        }
        public SimpleModel AddSimpleModel(SimpleModel simpleModel)
        {            
            simpleModels.Add(simpleModel);
            simpleModel.RenderType = SimpleModel.Type.LineList;
            return simpleModel;
        }
        public LightPoint AddLightPoint(Vector3 position, Color color, float intensity)
        {
            LightPoint lightPoint = new LightPoint(position, color, intensity);
            lightPoint.Model = lightPoint.GetDefaultModel(resourceDevice);
            lightPoints.Add(lightPoint);

            simpleModels.Add(lightPoint.Model);
            return lightPoint;
        }

        private float _lightIntensity;
        public float LightIntensity
        {
            get
            {
                return _lightIntensity;
            }
            set
            {
                _lightIntensity = value;
                foreach (LightPoint light in lightPoints)
                {
                    light.Intensity = LightIntensity;
                }
            }
        }
        public float AmbientIntensity
        {
            get;
            set;
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

        public void Draw(GraphicsDevice graphicsDevice, TimeSpan totalTime, Camera camera)
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

            foreach (MyModel myModel in myModels)
            {
                if (myModel.IsVisible)
                {
                    SetShaderEffect(ShaderEffect.NoEffect, graphicsDevice, myModel.WorldMatrix, camera);
                    myModel.Render(graphicsDevice);
                }

                SetShaderEffect(ShaderEffect.NoEffect, graphicsDevice, myModel.WorldMatrix, camera);
                VertexPositionColor[] vertices = new VertexPositionColor[4];
                vertices[0] = new VertexPositionColor(myModel.marker1, GlobalVars.Red);
                vertices[1] = new VertexPositionColor(myModel.marker2, GlobalVars.Red);
                vertices[2] = new VertexPositionColor(myModel.marker1, GlobalVars.Blue);
                vertices[3] = new VertexPositionColor(myModel.marker3, GlobalVars.Blue);
                VertexBuffer v = new VertexBuffer(graphicsDevice, VertexPositionColor.VertexDeclaration, vertices.Length, BufferUsage.WriteOnly);
                v.SetData(0, vertices, 0, vertices.Length, 0);
                graphicsDevice.SetVertexBuffer(v);
                graphicsDevice.DrawPrimitives(PrimitiveType.LineList, 0, vertices.Length / 2);
            }

            foreach (SimpleModel simpleModel in simpleModels)
            {
                if (simpleModel.IsVisible)
                {
                    SetShaderEffect(ShaderEffect.NoEffect, graphicsDevice, simpleModel.WorldMatrix, camera);
                    simpleModel.Render(graphicsDevice);
                }
            }
        }

        enum ShaderEffect { NoEffect, MyBasicEffect, BasicEffect };
        private void SetShaderEffect(ShaderEffect shaderEffect, GraphicsDevice graphicsDevice, Matrix world, Camera camera)
        {
            if(shaderEffect == ShaderEffect.NoEffect)
            {
                noEffect.World = world;
                noEffect.Projection = camera.projection;
                noEffect.View = camera.view;

                noEffect.Device = graphicsDevice;
                noEffect.Apply();
            }
            else if (shaderEffect == ShaderEffect.MyBasicEffect)
            {
                myBasicEffect.World = world;
                myBasicEffect.Projection = camera.projection;
                myBasicEffect.View = camera.view;

                if (lightPoints.Count > 0)
                {
                    myBasicEffect.DiffuseSource1 = lightPoints[0].Position;                    
                    myBasicEffect.DiffuseColor1 = lightPoints[0].LightColor;
                    myBasicEffect.DiffuseIntensity1 = lightPoints[0].Intensity;
                }

                if (lightPoints.Count > 1)
                {
                    myBasicEffect.DiffuseSource2 = lightPoints[1].Position;                    
                    myBasicEffect.DiffuseColor2 = lightPoints[1].LightColor;
                    myBasicEffect.DiffuseIntensity2 = lightPoints[1].Intensity;
                }

                if (lightPoints.Count > 2)
                {
                    myBasicEffect.DiffuseSource3 = lightPoints[2].Position;                    
                    myBasicEffect.DiffuseColor3 = lightPoints[2].LightColor;
                    myBasicEffect.DiffuseIntensity3 = lightPoints[2].Intensity;
                }

                myBasicEffect.AmbientIntensity = AmbientIntensity;
                myBasicEffect.Device = graphicsDevice;
                myBasicEffect.Apply();
            }
            else if (shaderEffect == ShaderEffect.BasicEffect)
            {
                //basicEffect.World = Matrix.Identity;
                //basicEffect.View = camera.view;
                //basicEffect.Projection = camera.projection;
                //basicEffect.CameraPosition = camera.cameraPosition;
                //basicEffect.LightPosition = xLightSource1;
                //basicEffect.AmbientColor = DiffuseColor;
                //basicEffect.DiffuseColor = AmbientColor;
                //basicEffect.EmissiveColor = Color.Black;
                //basicEffect.DiffuseTexture = texture;
                //basicEffect.Device = graphicsDevice;
                //basicEffect.Apply();
            }
        }
    }
}
