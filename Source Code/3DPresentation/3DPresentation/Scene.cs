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

namespace _3DPresentation
{
    /// <summary>
    /// Represents the 3D scene. Manages the camera (view / projection)
    /// transforms as well as a single Cube.
    /// </summary>
    public class Scene
    {
        Matrix view; // The view or camera transform
        Matrix projection; // The projection transform to convert 3D space to 2D screen space

        // The single Cube at the root of the scene
        SceneModel sceneModel = new SceneModel(false);

        float x = 0;
        float y = 0;
        float z = 1000;
        public Scene()
        {
            UpdateView();
        }

        private void UpdateView()
        {
            Vector3 cameraPosition = new Vector3(x, y, z); // the camera's position
            //Vector3 cameraTarget = Vector3.Zero; // the place the camera is looking (towards world origin)

            Vector3 cameraTarget = new Vector3(0, 0, -1000);
            // the transform representing a camera at a position looking at a target
            view = Matrix.CreateLookAt(cameraPosition, cameraTarget, Vector3.Up);
        }

        public float AspectRatio
        {
            set
            {
                // update the screen space transform every time the aspect ratio changes
                projection = Matrix.CreatePerspectiveFieldOfView(MathHelper.PiOver4, value, 1.0f, 30000.0f);
                //projection = Matrix.CreatePerspectiveFieldOfView(MathHelper.PiOver4, value, 1.0f, 100);
            }
        }

        public float LightSourceX
        {
            get
            {
                return sceneModel.LightSourceX;
            }
            set
            {
                sceneModel.LightSourceX = value;
            }
        }

        public float LightSourceY
        {
            get
            {
                return sceneModel.LightSourceY;
            }
            set
            {
                sceneModel.LightSourceY = value;
            }
        }

        public float LightSourceZ
        {
            get
            {
                return sceneModel.LightSourceZ;
            }
            set
            {
                sceneModel.LightSourceZ = value;
            }
        }

        public float LightIntensity
        {
            get
            {
                return sceneModel.LightIntensity;
            }
            set
            {
                sceneModel.LightIntensity = value;
            }
        }
        public float AmbientIntensity
        {
            get
            {
                return sceneModel.AmbientIntensity;
            }
            set
            {
                sceneModel.AmbientIntensity = value;
            }
        }

        public float X
        {
            get
            {
                return x;
            }
            set
            {
                x = value;
                UpdateView();
            }
        }
        public float Y
        {
            get
            {
                return y;
            }
            set
            {
                y = value;
                UpdateView();
            }
        }
        public float Z
        {
            get
            {
                return z;
            }
            set
            {
                z = value;
                UpdateView();
            }
        }

        public int FPS
        {
            get { return sceneModel.FPS; }
        }

        public void Draw(GraphicsDevice graphicsDevice, TimeSpan totalTime)
        {
            // clear the existing render target
            graphicsDevice.Clear(ClearOptions.Target | ClearOptions.DepthBuffer, Color.Transparent, 1.0f, 0);

            // draw the Cube
            sceneModel.Draw(graphicsDevice, totalTime, view * projection);
        }
    }
}
