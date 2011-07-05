// ===================================================================================
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//  THIS CODE AND INFORMATION IS PROVIDED "AS IS" WITHOUT WARRANTY
//  OF ANY KIND, EITHER EXPRESSED OR IMPLIED, INCLUDING BUT NOT
//  LIMITED TO THE IMPLIED WARRANTIES OF MERCHANTABILITY AND
//  FITNESS FOR A PARTICULAR PURPOSE.
// ===================================================================================
using System;
using System.Net;
using System.Windows;
using Microsoft.Xna.Framework;
using Microsoft.Xna.Framework.Graphics;
using _3DPresentation.Models;
using System.Windows.Controls;
using _3DPresentation.Models.PointModel;
using System.IO;
using _3DPresentation.Models.FaceModel;

namespace _3DPresentation
{
    /// <summary>
    /// Represents the 3D scene. Manages the camera (view / projection)
    /// transforms as well as a single Cube.
    /// </summary>
    public class Scene
    {
        Camera camera;
        public Vector2 ScreenSize { get; set; }
        // The single Cube at the root of the scene
        SceneModel sceneModel = new SceneModel(false);
        public Scene()
        {
            camera.cameraPosition = new Vector3(0, 0, 1.0f);
            camera.cameraTarget = new Vector3(0, 0, -1.0f);
            UpdateView2();

            GlobalVars.Light1 = new Vector3(0, 0, -1.0f);
        }

        public void  Scene_Draw(object sender, DrawEventArgs e)
        {
            // clear the existing render target
            GraphicsDevice graphicsDevice = e.GraphicsDevice;
            graphicsDevice.Clear(ClearOptions.Target | ClearOptions.DepthBuffer, Color.Transparent, 1.0f, 0);

            // draw 
            sceneModel.Draw(graphicsDevice, e.TotalTime, camera, ScreenSize);
        }

        // update the aspect ratio of the scene based on the
        // dimensions of the surface
        public void Scene_SizeChanged(object sender, SizeChangedEventArgs e)
        {
            DrawingSurface surface = sender as DrawingSurface;            
            AspectRatio = (float)surface.ActualWidth / (float)surface.ActualHeight;
            ScreenSize = new Vector2((float)surface.ActualWidth, (float)surface.ActualHeight);
        }

        public MyModel AddMyModel(string image, string depthmap, Vector3 position)
        {
            return sceneModel.AddMyModel(image, depthmap, position);
        }
        public SimpleModel AddSimpleModel(VertexPositionColor[] vertices, Vector3 position)
        {
            return sceneModel.AddSimpleModel(vertices, position);
        }
        public PointModel AddPointModel(FileInfo file)
        {
            return sceneModel.AddPointModel(file);
        }
        public FaceModel AddFaceModel(FileInfo file)
        {
            return sceneModel.AddFaceModel(file);
        }

        public FaceModel AddLightModel(FileInfo file)
        {
            return sceneModel.AddLightModel(file);
        }

        #region NewUpdate
        
        public void UpdateView2()
        {
            // the transform representing a camera at a position looking at a target
            camera.view = Matrix.CreateLookAt(camera.cameraPosition, camera.cameraTarget, Vector3.Up);
        }

        public GlobalVars.LOD LOD
        {
            get
            {
                return GlobalVars.LevelOfDetail;
            }
            set
            {
                GlobalVars.LevelOfDetail = value;
            }
        }

        public Vector3 CameraPosition
        {
            get
            {
                return camera.cameraPosition;
            }
            set
            {
                camera.cameraPosition = value;
            }
        }

        public Vector3 CameraTarget
        {
            get
            {
                return camera.cameraTarget;
            }
            set
            {
                camera.cameraTarget = value;
            }
        }
        #endregion

        public float AspectRatio
        {
            set
            {
                // update the screen space transform every time the aspect ratio changes
                camera.projection = Matrix.CreatePerspectiveFieldOfView(MathHelper.PiOver4, value, 0.1f, 10.0f);
            }
        }       
            
        public int FPS
        {
            get { return sceneModel.FPS; }
        }
    }
}
