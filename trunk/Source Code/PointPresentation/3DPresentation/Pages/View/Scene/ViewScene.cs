using Babylon.Toolbox;
using System.Windows.Controls;
using Microsoft.Xna.Framework.Graphics;
using Microsoft.Xna.Framework.Silverlight;
using System;
using System.Windows;
using _3DPresentation.Models;
using Microsoft.Xna.Framework;

namespace _3DPresentation
{
    public partial class ViewScene
    {
        // the device to use when creating resources
        static readonly GraphicsDevice resourceDevice = GraphicsDeviceManager.Current.GraphicsDevice;

        OrbitCamera Camera = new OrbitCamera { Alpha = -0.4f };
        private UserControl Container;
        private DrawingSurface Surface { get; set; }

        Vector2 SurfaceSize { get; set; }

        // States
        volatile bool IsAddingModel;

        // Notification
        public int FPS
        {
            get;
            set;
        }

        // Target Model
        public BaseModel TargetModel { get; private set; }

        public ViewScene(UserControl container, DrawingSurface surface)
        {
            Container = container;
            Surface = surface;

            Surface.SizeChanged += new System.Windows.SizeChangedEventHandler(Surface_SizeChanged);
            Surface.Draw += new System.EventHandler<DrawEventArgs>(Surface_Draw);

            PrepareIO();
            PrepareModels();
            PrepareRender();
            PrepareInteraction();
        }
        
        int _total_frames = 0;
        DateTime _lastFPS = DateTime.Now;
        void Surface_Draw(object sender, DrawEventArgs e)
        {
            _total_frames++;
            if ((DateTime.Now - _lastFPS).Seconds >= 1)
            {
                FPS = _total_frames;
                _total_frames = 0;
                _lastFPS = DateTime.Now;
            }

            GraphicsDevice graphicsDevice = e.GraphicsDevice;
            graphicsDevice.Clear(ClearOptions.Target | ClearOptions.DepthBuffer, Color.Black, 1.0f, 0);
            Render(graphicsDevice);

            Camera.ApplyInertia();

            e.InvalidateSurface();
        }

        void Surface_SizeChanged(object sender, System.Windows.SizeChangedEventArgs e)
        {
            SurfaceSize = new Vector2((float)Surface.ActualWidth, (float)Surface.ActualHeight);
            Camera.AspectRatio = (float)(Surface.ActualWidth / Surface.ActualHeight);
        }

    }
}
