﻿using _3DPresentation.Effects;
using System.Collections.Generic;
using _3DPresentation.Models;
using Microsoft.Xna.Framework.Graphics;
using System;
using Microsoft.Xna.Framework;
using System.IO;
using System.Windows.Threading;
using System.Windows;
using System.Windows.Controls;

namespace _3DPresentation
{
    public partial class CustomScene : Babylon.Scene
    {
        // Babylon
        private Babylon.BabylonSurface Surface { get; set; }
        private UserControl Container { get; set; }
        private GraphicsDevice Device { get { return Engine.Device; } }

        // States
        public bool IsLoaded { get; private set; }
        volatile bool IsAddingModel;
        
        // Notifications
        BaseModel Target;
        public Vector3 CameraPosition { get { return ActiveCamera.Position; } }
        public Vector3 TargetPosition
        {
            get
            {
                if (ActiveCamera != null)
                    return new Vector3(ActiveCamera.RotationX, ActiveCamera.RotationY, ActiveCamera.RotationZ);
                return Vector3.Zero;
            }
        }

        public CustomScene(UserControl container, Babylon.BabylonSurface babylonSurface, string name, Babylon.Engine engine)
            : base(name, engine)
        {
            // Init local variables
            Container = container;
            Surface = babylonSurface;
            
            // State
            IsLoaded = false;
            IsAddingModel = false;

            // Init Events
            this.Loaded += new EventHandler(CustomScene_Loaded);
        }

        void CustomScene_Loaded(object sender, EventArgs e)
        {
            IsLoaded = true;

            PrepareIO();
            PrepareStreaming();
            PrepareModels();
            PrepareRender();
            PrepareInteraction();
        }


        public bool IsFlyTo { get; private set; }
        public void GoToModel(BaseModel model)
        {
            if (customSceneModels.Contains(model))
            {
                
            }
        }
    }
}
