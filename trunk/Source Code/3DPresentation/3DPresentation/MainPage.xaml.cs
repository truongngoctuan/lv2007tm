using System;
using System.Collections.Generic;
using System.Linq;
using System.Net;
using System.Windows;
using System.Windows.Controls;
using System.Windows.Documents;
using System.Windows.Input;
using System.Windows.Media;
using System.Windows.Media.Animation;
using System.Windows.Shapes;
using Microsoft.Xna.Framework.Graphics;

namespace _3DPresentation
{
    public partial class MainPage : UserControl
    {
        // init the 3D scene
        Scene scene = new Scene();

        public MainPage()
        {
            InitializeComponent();
        }

        void OnDraw(object sender, DrawEventArgs args)
        {
            // draw 3D scene
            scene.Draw(args.GraphicsDevice, args.TotalTime);

            // invalidate to get a callback next frame
            args.InvalidateSurface();
        }

        // update the aspect ratio of the scene based on the
        // dimensions of the surface
        private void OnSizeChanged(object sender, SizeChangedEventArgs e)
        {
            DrawingSurface surface = sender as DrawingSurface;
            scene.AspectRatio = (float)surface.ActualWidth / (float)surface.ActualHeight;
        }
    }
}
