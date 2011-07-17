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
using Babylon.Toolbox;

namespace _3DPresentation
{
    public partial class CustomScene : Babylon.Scene, IBaseScene
    {
        // Babylon
        private Babylon.BabylonSurface Surface { get; set; }
        private UserControl Container { get; set; }
        private GraphicsDevice Device { get { return Engine.Device; } }
        Vector2 SurfaceSize { get; set; }
        // States
        public bool IsLoaded { get; private set; }
        public bool IsEnable { get; set; }
        
        // StatesManager
        public StatesManager StatesManager;

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
            IsEnable = false;
            IsLoaded = false;            
            
            // Init Events
            this.Loaded += new EventHandler(CustomScene_Loaded);
            Surface.SizeChanged += new SizeChangedEventHandler(Surface_SizeChanged);

            // resourceDevice is only used to init, can't draw with this resourceDevice
            if (engine.Device == null)
            {
                engine.Device = GlobalVars.resourceDevice;
            }
        }

        void Surface_SizeChanged(object sender, SizeChangedEventArgs e)
        {
            SurfaceSize = new Vector2((float)Surface.ActualWidth, (float)Surface.ActualHeight);
        }

        void CustomScene_Loaded(object sender, EventArgs e)
        {
            IsLoaded = true;
            IsEnable = true;

            PrepareIO();
            PrepareStreaming();
            PrepareModels();
            PrepareRender();
            PrepareInteraction();

            Vertices = new Babylon.Toolbox.VertexPositionNormalTexture[4];
            Indices = new ushort[] { 0, 1, 2, 1, 2, 3 };
            Vertices[0].Position = new Vector3(-2, -2, 0); Vertices[0].Normal = new Vector3(0, 0, 1); Vertices[0].TextureCoordinates = new Vector2(0, 1);
            Vertices[1].Position = new Vector3(-2, 2, 0); Vertices[1].Normal = new Vector3(0, 0, 1); Vertices[1].TextureCoordinates = new Vector2(0, 0);
            Vertices[2].Position = new Vector3(2, -2, 0); Vertices[2].Normal = new Vector3(0, 0, 1); Vertices[2].TextureCoordinates = new Vector2(1, 1);
            Vertices[3].Position = new Vector3(2, 2, 0); Vertices[3].Normal = new Vector3(0, 0, 1); Vertices[3].TextureCoordinates = new Vector2(1, 0);
        }
        public Babylon.Toolbox.VertexPositionNormalTexture[] Vertices;
        public ushort[] Indices;
        public override void Render()
        {
            if (IsEnable == false)
                return;

            if(StatesManager == null)
                StatesManager = new StatesManager(Device);
            base.Render();
        }

        public override void RenderExtendedStandardModel()
        {
            EffectManager.Scene = this;
            Render(Device);
        }

        public override void RenderExtendedOpacityModel()
        {
            
        }

        public override void RenderExtendedAlphaModel()
        {
            
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
            return SurfaceSize;
        }

        StatesManager IBaseScene.GetStatesManager()
        {
            return StatesManager;
        }

        #endregion
    }
}
