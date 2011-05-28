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
            //App.Current.Host.Settings.MaxFrameRate = 24;            

            LayoutRoot.KeyDown += new KeyEventHandler(LayoutRoot_KeyDown);
            myLightSourceX.ValueChanged += new MySliderControl.ValueChangedEventHandler(myLightSourceX_ValueChanged);
            myLightSourceY.ValueChanged += new MySliderControl.ValueChangedEventHandler(myLightSourceY_ValueChanged);
            myLightSourceZ.ValueChanged += new MySliderControl.ValueChangedEventHandler(myLightSourceZ_ValueChanged);

            myLightIntensity.ValueChanged += new MySliderControl.ValueChangedEventHandler(myDiffuseIntensity_ValueChanged);
            myAmbientIntensity.ValueChanged += new MySliderControl.ValueChangedEventHandler(myAmbientIntensity_ValueChanged);


            // Init
            myLightSourceX.MinValue = -1000;
            myLightSourceY.MinValue = -1000;
            myLightSourceZ.MinValue = -3000;

            myLightSourceX.MaxValue = 1000;
            myLightSourceY.MaxValue = 1000;
            myLightSourceZ.MaxValue = 3000;

            myLightIntensity.MinValue = 0;
            myLightIntensity.MaxValue = 5000;

            myAmbientIntensity.MinValue = 0;
            myAmbientIntensity.MaxValue = 1.0;


            myLightSourceX.Value = 0;
            myLightSourceY.Value = 0;
            myLightSourceZ.Value = 1000;
            myLightIntensity.Value = 5000.0f;
            myAmbientIntensity.Value = 0.2f;
        }

        void myAmbientIntensity_ValueChanged(object sender, MySliderControl.ValueChangedEventArgs e)
        {
            scene.AmbientIntensity = (float)e.NewValue;
        }

        void myDiffuseIntensity_ValueChanged(object sender, MySliderControl.ValueChangedEventArgs e)
        {
            scene.LightIntensity = (float)e.NewValue;
        }

        void myLightSourceZ_ValueChanged(object sender, MySliderControl.ValueChangedEventArgs e)
        {
            scene.LightSourceZ = (float)e.NewValue;
        }

        void myLightSourceY_ValueChanged(object sender, MySliderControl.ValueChangedEventArgs e)
        {
            scene.LightSourceY = (float)e.NewValue;
        }

        void myLightSourceX_ValueChanged(object sender, MySliderControl.ValueChangedEventArgs e)
        {
            scene.LightSourceX = (float)e.NewValue;
        }

        void LayoutRoot_KeyDown(object sender, KeyEventArgs e)
        {
            if (e.Key == Key.A)
                scene.X -= 10;
            if (e.Key == Key.D)
                scene.X += 10;

            if (e.Key == Key.W)
                scene.Y += 10;
            if (e.Key == Key.S)
                scene.Y -= 10;

            if (e.Key == Key.Q)
                scene.Z -= 10;
            if (e.Key == Key.E)
                scene.Z += 10;
        }

        void OnDraw(object sender, DrawEventArgs args)
        {
            if (isDraw)
            {
                // draw 3D scene
                scene.Draw(args.GraphicsDevice, args.TotalTime);

                // invalidate to get a callback next frame
                args.InvalidateSurface();
            }
        }

        // update the aspect ratio of the scene based on the
        // dimensions of the surface
        private void OnSizeChanged(object sender, SizeChangedEventArgs e)
        {
            DrawingSurface surface = sender as DrawingSurface;
            scene.AspectRatio = (float)surface.ActualWidth / (float)surface.ActualHeight;
        }

        bool isDraw = false;
        private void button1_Click(object sender, RoutedEventArgs e)
        {
            isDraw = !isDraw;
            if(isDraw)
                button1.Content = "Stop";
            else
                button1.Content = "Start";
            drawingSurface.Invalidate();
        }

        private void XSlider_ValueChanged(object sender, RoutedPropertyChangedEventArgs<double> e)
        {
            float value = (float)e.NewValue;
            scene.X = value;
        }

        private void YSlider_ValueChanged(object sender, RoutedPropertyChangedEventArgs<double> e)
        {
            float value = (float)e.NewValue;
            scene.Y = value;
        }

        private void ZSlider_ValueChanged(object sender, RoutedPropertyChangedEventArgs<double> e)
        {
            float value = (float)e.NewValue;
            scene.Z = value;
        }
    }
}
