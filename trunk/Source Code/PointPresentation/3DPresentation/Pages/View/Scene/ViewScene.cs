using Babylon.Toolbox;
using System.Windows.Controls;
using Microsoft.Xna.Framework.Graphics;
using Microsoft.Xna.Framework.Silverlight;
using System;
using System.Windows;
using _3DPresentation.Models;
using Microsoft.Xna.Framework;
using _3DPresentation.Effects;

namespace _3DPresentation
{
    public partial class ViewScene : IBaseScene
    {
        // the device to use when creating resources
        //static readonly GraphicsDevice resourceDevice = GraphicsDeviceManager.Current.GraphicsDevice;
        OrbitCamera _camera = new OrbitCamera { Alpha = (float)Math.PI / 2 };

        public OrbitCamera Camera
        {
            get { return _camera; }
            set { _camera = value; }
        }
        private UserControl Container;
        private DrawingSurface Surface { get; set; }

        public StatesManager StatesManager;
        public bool WireFrame;
        Vector2 SurfaceSize { get; set; }

        // States
        public bool IsLoaded { get; private set; }
        public bool IsEnable { get; set; }

        // Notification
        public int FPS { get; private set; }
        public int DrawError { get; private set; }

        // Target Model
        public BaseModel TargetModel { get; private set; }

        public ViewScene(UserControl container, DrawingSurface surface)
        {
            Container = container;
            Surface = surface;

            // State
            IsEnable = false;
            IsLoaded = false;

            Surface.SizeChanged += new System.Windows.SizeChangedEventHandler(Surface_SizeChanged);
            Surface.Draw += new System.EventHandler<DrawEventArgs>(Surface_Draw);

            InitScene();
        }

        private void InitScene()
        {
            IsLoaded = true;
            IsEnable = true;

            PrepareIO();
            PrepareModels();
            PrepareRender();
            PrepareInteraction();
        }
        
        int _total_frames = 0;
        DateTime _lastFPS = DateTime.Now;

        Color _backgroundColor = Color.Black;

        public Color BackgroundColor
        {
            get { return _backgroundColor; }
            set { _backgroundColor = value; }
        }
        void Surface_Draw(object sender, DrawEventArgs e)
        {
            if (IsEnable == false)
                return;

            _total_frames++;
            if ((DateTime.Now - _lastFPS).Seconds >= 1)
            {
                FPS = _total_frames;
                _total_frames = 0;
                _lastFPS = DateTime.Now;
            }

            EffectManager.Scene = this;
            GraphicsDevice graphicsDevice = e.GraphicsDevice;
            if (graphicsDevice == null)
                return;

            if (StatesManager == null)
            {
                StatesManager = new StatesManager(graphicsDevice);
            }

            Render(graphicsDevice);
            _camera.ApplyInertia();

            e.InvalidateSurface();
        }

        void Surface_SizeChanged(object sender, System.Windows.SizeChangedEventArgs e)
        {
            SurfaceSize = new Vector2((float)Surface.ActualWidth, (float)Surface.ActualHeight);
            _camera.AspectRatio = (float)(Surface.ActualWidth / Surface.ActualHeight);
        }


        #region IBaseScene Members

        Vector3 IBaseScene.GetCameraPosition()
        {
            return Camera.Position;
        }

        Matrix IBaseScene.GetCameraView()
        {
            return Camera.View;
        }

        Matrix IBaseScene.GetCameraProjection()
        {
            return Camera.Projection;
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
