﻿using System;
using System.Net;
using System.Windows;
using Microsoft.Xna.Framework;
using Microsoft.Xna.Framework.Graphics;
using Microsoft.Xna.Framework.Silverlight;
using System.IO;
using System.Windows.Media.Imaging;
using Babylon.Toolbox;
using System.Windows.Threading;
using System.Collections.Generic;
using _3DPresentation.Models;
using _3DPresentation.Models.PointModel;
using _3DPresentation.Effects.PointEffect;
using _3DPresentation.Effects.MyBasicEffect;
using _3DPresentation.Effects.NoEffect;
using _3DPresentation.Models.FaceModel;

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
        PointEffect pointEffect;
        
        List<MyModel> myModels;
        List<SimpleModel> simpleModels;
        List<PointModel> pointModels;
        List<FaceModel> faceModels;

        public SceneModel(bool solidFaceColor = true)
        {
            myModels = new List<MyModel>();
            simpleModels = new List<SimpleModel>();
            pointModels = new List<PointModel>();
            faceModels = new List<FaceModel>();

            noEffect = new NoEffect(resourceDevice);
            myBasicEffect = new MyBasicEffect(resourceDevice);
            basicEffect = new BasicEffect(resourceDevice);
            pointEffect = new PointEffect(resourceDevice);
        }

        public MyModel AddMyModel(string imagePath, string depthmapPath, Vector3 position)
        {
            bIsLoading = true;
            MyModel myModel = new MyModel(imagePath, depthmapPath, 640, 480);
            myModel.WorldMatrix = Matrix.CreateTranslation(position);
            myModel.Init(resourceDevice);
            myModels.Add(myModel);
            bIsLoading = false;
            return myModel;
        }
        public SimpleModel AddSimpleModel(VertexPositionColor[] vertices, Vector3 position)
        {
            bIsLoading = true;
            SimpleModel simpleModel = SimpleModel.CreateModel(resourceDevice, vertices);
            simpleModel.WorldMatrix = Matrix.CreateTranslation(position);
            simpleModel.RenderType = SimpleModel.Type.LineList;
            simpleModels.Add(simpleModel);
            bIsLoading = false;
            return simpleModel;
        }
        public SimpleModel AddSimpleModel(SimpleModel simpleModel)
        {
            bIsLoading = true;
            simpleModels.Add(simpleModel);
            simpleModel.RenderType = SimpleModel.Type.LineList;
            bIsLoading = false;
            return simpleModel;
        }
        public PointModel AddPointModel(FileInfo file)
        {
            bIsLoading = true;
            PointModel pointModel = PointModel.Import(file);
            if (pointModel != null)
            {
                pointModel.InitBuffers(resourceDevice);
                pointModels.Add(pointModel);
            }
            bIsLoading = false;
            return pointModel;
        }

        public FaceModel AddFaceModel(FileInfo file)
        {
            bIsLoading = true;
            FaceModel faceModel = FaceModel.Import(file);
            if (faceModel != null)
            {
                faceModel.InitBuffers(resourceDevice);
                faceModels.Add(faceModel);
            }
            bIsLoading = false;
            return faceModel;
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

        volatile bool bIsLoading = false;
        public void Draw(GraphicsDevice graphicsDevice, TimeSpan totalTime, Camera camera, Vector2 screenSize)
        {
            if(bIsLoading)
                return;
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
                    SetShaderEffect(_3DPresentation.GlobalVars.ShaderEffect.NoEffect, graphicsDevice, myModel.WorldMatrix, camera, screenSize);
                    myModel.Render(graphicsDevice);
                }
            }

            foreach (SimpleModel simpleModel in simpleModels)
            {
                if (simpleModel.IsVisible)
                {
                    SetShaderEffect(_3DPresentation.GlobalVars.ShaderEffect.NoEffect, graphicsDevice, simpleModel.WorldMatrix, camera, screenSize);
                    simpleModel.Render(graphicsDevice);
                }
            }

            foreach (PointModel pointModel in pointModels)
            {
                if (pointModel.IsVisible)
                {                    
                    SetShaderEffect(_3DPresentation.GlobalVars.ShaderEffect.PointEffect, graphicsDevice, pointModel.WorldMatrix, camera, screenSize);
                    pointModel.Render(graphicsDevice);
                    //break;
                }
            }

            foreach (FaceModel faceModel in faceModels)
            {
                if (faceModel.IsVisible)
                {
                    SetShaderEffect(_3DPresentation.GlobalVars.ShaderEffect.MyBasicEffect, graphicsDevice, faceModel.WorldMatrix, camera, screenSize);
                    faceModel.Render(graphicsDevice);
                    //break;
                }
            }
        }

        private void SetShaderEffect(_3DPresentation.GlobalVars.ShaderEffect shaderEffect, GraphicsDevice graphicsDevice, Matrix world, Camera camera, Vector2 screenSize)
        {
            if (shaderEffect == _3DPresentation.GlobalVars.ShaderEffect.NoEffect)
            {
                noEffect.World = world;
                noEffect.Projection = camera.projection;
                noEffect.View = camera.view;

                noEffect.Device = graphicsDevice;
                noEffect.Apply();
            }
            else if (shaderEffect == _3DPresentation.GlobalVars.ShaderEffect.MyBasicEffect)
            {
                myBasicEffect.World = world;
                myBasicEffect.Projection = camera.projection;
                myBasicEffect.View = camera.view;

                myBasicEffect.DiffuseIntensity1 = 1.0f;
                myBasicEffect.DiffuseColor1 = GlobalVars.Green;
                myBasicEffect.DiffuseSource1 = GlobalVars.Light1;

                myBasicEffect.DiffuseIntensity2 = 0;
                myBasicEffect.DiffuseIntensity3 = 0;
                myBasicEffect.AmbientIntensity = 0.3f;

                myBasicEffect.Device = graphicsDevice;
                myBasicEffect.Apply();
                // removed
            }
            else if (shaderEffect == _3DPresentation.GlobalVars.ShaderEffect.BasicEffect)
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
            else if (shaderEffect == _3DPresentation.GlobalVars.ShaderEffect.PointEffect)
            {
                pointEffect.World = world;
                pointEffect.Projection = camera.projection;
                pointEffect.View = camera.view;
                pointEffect.Scale = new Vector2(1.0f / screenSize.X, 1.0f / screenSize.Y);

                pointEffect.Device = graphicsDevice;
                pointEffect.Apply();
            }
        }
    }
}