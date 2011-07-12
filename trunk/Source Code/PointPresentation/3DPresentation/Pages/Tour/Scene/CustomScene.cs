using _3DPresentation.Effects;
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
    public partial class CustomScene : Babylon.Scene, IBaseScene
    {
        // Babylon
        private Babylon.BabylonSurface Surface { get; set; }
        private UserControl Container { get; set; }
        private GraphicsDevice Device { get { return Engine.Device; } }

        // States
        public bool IsLoaded { get; private set; }
        public bool IsEnable { get; set; }
        
        // Notifications
        public float FPS
        {
            get { return Engine.FPS; }
        }
        public BaseModel Target
        {
            get { return selectedMesh; }
        }
        public Vector3 CameraPosition { get { return ActiveCamera.Position; } }
        public Vector3 TargetPosition
        {
            get
            {
                if (ActiveCamera != null)
                    return new Vector3(DrawError, ActiveCamera.RotationY, ActiveCamera.RotationZ);
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
            IsEnable = true;
            IsLoaded = false;            
            
            // Init Events
            this.Loaded += new EventHandler(CustomScene_Loaded);

            // resourceDevice is only used to init, can't draw with this resourceDevice
            if (engine.Device == null)
            {
                engine.Device = GlobalVars.resourceDevice;
            }
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

        public override void Render()
        {
            if (IsEnable == false)
                return;
            try
            {
                base.Render();

                EffectManager.Scene = this;
                Render(Device);
            }
            catch (ArgumentException ex)
            {
                DrawError++;
            }

            if (Drawed != null)
                Drawed(this, EventArgs.Empty);
        }

        public bool IsFlyTo { get; private set; }
        public void GoToModel(BaseModel model)
        {

        }

        #region IBaseScene Members

        Vector3 IBaseScene.GetCameraPosition()
        {
            return ActiveCamera.Position;
        }

        Matrix IBaseScene.GetCameraView()
        {
            return ActiveCamera.View;
        }

        Matrix IBaseScene.GetCameraProjection()
        {
            return ActiveCamera.Projection;
        }

        Vector2 IBaseScene.GetDrawingSurfaceSize()
        {
            return new Vector2(Convert.ToSingle(Surface.ActualWidth), Convert.ToSingle(Surface.ActualHeight));
        }

        #endregion
    }
}
