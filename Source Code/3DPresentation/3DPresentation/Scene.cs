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
        SceneModel Cube = new SceneModel(false);

        public Scene()
        {
            Vector3 cameraPosition = new Vector3(0, 0, 5.0f); // the camera's position
            Vector3 cameraTarget = Vector3.Zero; // the place the camera is looking (towards world origin)

            // the transform representing a camera at a position looking at a target
            view = Matrix.CreateLookAt(cameraPosition, cameraTarget, Vector3.Up);
        }

        public float AspectRatio
        {
            set
            {
                // update the screen space transform every time the aspect ratio changes
                projection = Matrix.CreatePerspectiveFieldOfView(MathHelper.PiOver4, value, 1.0f, 100.0f);
            }
        }

        public void Draw(GraphicsDevice graphicsDevice, TimeSpan totalTime)
        {
            // clear the existing render target
            graphicsDevice.Clear(ClearOptions.Target | ClearOptions.DepthBuffer, Color.Transparent, 1.0f, 0);

            // draw the Cube
            Cube.Draw(graphicsDevice, totalTime, view * projection);
        }
    }
}
