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

        private static int MAX_FRAME_RATE = 24;
        public MainPage()
        {
            InitializeComponent();
            //Timeline.DesiredFrameRateProperty.OverrideMetadata(typeof(Timeline), new FrameworkPropertyMetadata { DefaultValue = 24 });
            // INGNORED
            App.Current.Host.Settings.MaxFrameRate = MAX_FRAME_RATE;            
            
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

            CompositionTarget.Rendering += new EventHandler(CompositionTarget_Rendering);

            myUDRMZControl.MoveForwardClick += new RoutedEventHandler(MoveForward_Click);
            myUDRMZControl.MoveBackClick += new RoutedEventHandler(MoveBack_Click);
            myUDRMZControl.MoveLeftClick += new RoutedEventHandler(MoveLeft_Click);
            myUDRMZControl.MoveRightClick += new RoutedEventHandler(MoveRight_Click);

            myUDRMZControl.RotateLeftClick += new RoutedEventHandler(RotateLeft_Click);
            myUDRMZControl.RotateRightClick += new RoutedEventHandler(RotateRight_Click);

            myUDRMZControl.RotateUpClick += new RoutedEventHandler(RotateUp_Click);
            myUDRMZControl.RotateDownClick += new RoutedEventHandler(RotateDown_Click);
        }
        
        int uiFPS = 0;
        int _total_frames = 0;
        DateTime _lastFPS = DateTime.Now;            
        void CompositionTarget_Rendering(object sender, EventArgs e)
        {
            _total_frames++;
            if ((DateTime.Now - _lastFPS).Seconds >= 1)
            {
                uiFPS = _total_frames;
                _total_frames = 0;
                _lastFPS = DateTime.Now;
            }
            myUIFPS.Dispatcher.BeginInvoke(new Action(() => { myUIFPS.Text = "UIFPS : " + uiFPS; }));
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

        void OnDraw(object sender, DrawEventArgs args)
        {
            myDrawFPS.Dispatcher.BeginInvoke(new Action(() => { myDrawFPS.Text = "DrawFPS : " + scene.FPS; }));
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
        bool isStart = false;
        private void button1_Click(object sender, RoutedEventArgs e)
        {
            isDraw = !isDraw;
            if (isDraw)
            {
                button1.Content = "Stop";
                isStart = true;
            }
            else
            {
                button1.Content = "Start";
                isStart = false;
            }
            drawingSurface.Invalidate();
        }

        #region NewMove
        private void MoveForward_Click(object sender, RoutedEventArgs e)
        {
            //scene.Y += 10;
            try
            {
                if (isStart)
                {
                    CameraMovements.Move(scene.CameraPosition, scene.CameraTarget, 10.0f, _3DPresentation.CameraMovements.MOVE.FORWARD);
                    scene.CameraPosition = CameraMovements.CameraResult;
                    scene.CameraTarget = CameraMovements.LookAtResult;
                    scene.UpdateView2();
                }
            }
            catch (Exception ex)
            {
                MessageBox.Show("MoveForward_Click" + ex.Message);
            }

        }

        private void MoveBack_Click(object sender, RoutedEventArgs e)
        {
            //scene.Y += 10;
            try
            {
                if (isStart)
                {
                    CameraMovements.Move(scene.CameraPosition, scene.CameraTarget, 10.0f, _3DPresentation.CameraMovements.MOVE.BACK);
                    scene.CameraPosition = CameraMovements.CameraResult;
                    scene.CameraTarget = CameraMovements.LookAtResult;
                    scene.UpdateView2();
                }
            }
            catch (Exception ex)
            {
                MessageBox.Show("MoveBack_Click" + ex.Message);
            }

        }

        private void MoveLeft_Click(object sender, RoutedEventArgs e)
        {
            //scene.Y += 10;
            try
            {
                if (isStart)
                {
                    CameraMovements.Move(scene.CameraPosition, scene.CameraTarget, 10.0f, _3DPresentation.CameraMovements.MOVE.LEFT);
                    scene.CameraPosition = CameraMovements.CameraResult;
                    scene.CameraTarget = CameraMovements.LookAtResult;
                    scene.UpdateView2();
                }
            }
            catch (Exception ex)
            {
                MessageBox.Show("MoveLeft_Click" + ex.Message);
            }

        }

        private void MoveRight_Click(object sender, RoutedEventArgs e)
        {
            //scene.Y += 10;
            try
            {
                if (isStart)
                {
                    CameraMovements.Move(scene.CameraPosition, scene.CameraTarget, 10.0f, _3DPresentation.CameraMovements.MOVE.RIGHT);
                    scene.CameraPosition = CameraMovements.CameraResult;
                    scene.CameraTarget = CameraMovements.LookAtResult;
                    scene.UpdateView2();
                }
            }
            catch (Exception ex)
            {
                MessageBox.Show("MoveRight_Click" + ex.Message);
            }

        }

        #endregion

        #region NewRotate
        private void RotateLeft_Click(object sender, RoutedEventArgs e)
        {
            //scene.Y += 10;
            try
            {
                if (isStart)
                {
                    CameraMovements.Rotate(new Microsoft.Xna.Framework.Vector2(0, -2), scene.CameraPosition, scene.CameraTarget);
                    //scene.CameraPosition = CameraMovements.CameraResult;
                    scene.CameraTarget = CameraMovements.LookAtResult;
                    scene.UpdateView2();
                }
            }
            catch (Exception ex)
            {
                MessageBox.Show("RotateLeft_Click" + ex.Message);
            }

        }

        private void RotateRight_Click(object sender, RoutedEventArgs e)
        {
            //scene.Y += 10;
            try
            {
                if (isStart)
                {
                    CameraMovements.Rotate(new Microsoft.Xna.Framework.Vector2(0, 2), scene.CameraPosition, scene.CameraTarget);
                    //scene.CameraPosition = CameraMovements.CameraResult;
                    scene.CameraTarget = CameraMovements.LookAtResult;
                    scene.UpdateView2();
                }
            }
            catch (Exception ex)
            {
                MessageBox.Show("RotateRight_Click" + ex.Message);
            }

        }

        private void RotateUp_Click(object sender, RoutedEventArgs e)
        {
            //scene.Y += 10;
            try
            {
                if (isStart)
                {
                    CameraMovements.Rotate(new Microsoft.Xna.Framework.Vector2(-2, 0), scene.CameraPosition, scene.CameraTarget);
                    //scene.CameraPosition = CameraMovements.CameraResult;
                    scene.CameraTarget = CameraMovements.LookAtResult;
                    scene.UpdateView2();
                }
            }
            catch (Exception ex)
            {
                MessageBox.Show("RotateUp_Click" + ex.Message);
            }

        }

        private void RotateDown_Click(object sender, RoutedEventArgs e)
        {
            //scene.Y += 10;
            try
            {
                if (isStart)
                {
                    CameraMovements.Rotate(new Microsoft.Xna.Framework.Vector2(2, 0), scene.CameraPosition, scene.CameraTarget);
                    //scene.CameraPosition = CameraMovements.CameraResult;
                    scene.CameraTarget = CameraMovements.LookAtResult;
                    scene.UpdateView2();
                }
            }
            catch (Exception ex)
            {
                MessageBox.Show("RotateDown_Click" + ex.Message);
            }

        }


        bool bIsbtDown = false;
        Point oldPoint = new Point();
        Point newPoint = new Point();

        private void LayoutRoot_MouseLeftButtonDown(object sender, MouseButtonEventArgs e)
        {
            //MessageBox.Show("LayoutRoot_MouseLeftButtonDown");
            bIsbtDown = true;
            oldPoint = e.GetPosition(drawingSurface);
        }

        private void LayoutRoot_MouseLeftButtonUp(object sender, MouseButtonEventArgs e)
        {
            bIsbtDown = false;
        }

        private void LayoutRoot_MouseMove(object sender, MouseEventArgs e)
        {
            if (bIsbtDown && isStart)
            {
                newPoint = e.GetPosition(drawingSurface);

                CameraMovements.Rotate(new Microsoft.Xna.Framework.Vector2((float)(newPoint.Y - oldPoint.Y), (float)(newPoint.X - oldPoint.X)), scene.CameraPosition, scene.CameraTarget);
                scene.CameraTarget = CameraMovements.LookAtResult;
                scene.UpdateView2();

                oldPoint = newPoint;
            }
        }
        #endregion
    }
}
