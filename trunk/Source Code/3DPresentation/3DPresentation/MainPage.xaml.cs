﻿using System;
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

            myLightSourceX2.ValueChanged += new MySliderControl.ValueChangedEventHandler(myLightSourceX2_ValueChanged);
            myLightSourceY2.ValueChanged += new MySliderControl.ValueChangedEventHandler(myLightSourceY2_ValueChanged);
            myLightSourceZ2.ValueChanged += new MySliderControl.ValueChangedEventHandler(myLightSourceZ2_ValueChanged);

            myLightSourceX3.ValueChanged += new MySliderControl.ValueChangedEventHandler(myLightSourceX3_ValueChanged);
            myLightSourceY3.ValueChanged += new MySliderControl.ValueChangedEventHandler(myLightSourceY3_ValueChanged);
            myLightSourceZ3.ValueChanged += new MySliderControl.ValueChangedEventHandler(myLightSourceZ3_ValueChanged);

            myLightIntensity.ValueChanged += new MySliderControl.ValueChangedEventHandler(myDiffuseIntensity_ValueChanged);
            myAmbientIntensity.ValueChanged += new MySliderControl.ValueChangedEventHandler(myAmbientIntensity_ValueChanged);

            // Init
            myLightSourceX.MinValue = -1000;
            myLightSourceY.MinValue = -1000;
            myLightSourceZ.MinValue = -3000;

            myLightSourceX.MaxValue = 1000;
            myLightSourceY.MaxValue = 1000;
            myLightSourceZ.MaxValue = 3000;

            myLightSourceX2.MinValue = -1000;
            myLightSourceY2.MinValue = -1000;
            myLightSourceZ2.MinValue = -3000;

            myLightSourceX2.MaxValue = 1000;
            myLightSourceY2.MaxValue = 1000;
            myLightSourceZ2.MaxValue = 3000;

            myLightSourceX3.MinValue = -1000;
            myLightSourceY3.MinValue = -1000;
            myLightSourceZ3.MinValue = -3000;

            myLightSourceX3.MaxValue = 1000;
            myLightSourceY3.MaxValue = 1000;
            myLightSourceZ3.MaxValue = 3000;

            myLightIntensity.MinValue = 0;
            myLightIntensity.MaxValue = 10000;

            myAmbientIntensity.MinValue = 0;
            myAmbientIntensity.MaxValue = 1.0;


            myLightSourceX.Value = 200;
            myLightSourceY.Value = 200;
            myLightSourceZ.Value = -500;

            myLightSourceX2.Value = -300;
            myLightSourceY2.Value = 200;
            myLightSourceZ2.Value = -500;

            myLightSourceX3.Value = 700;
            myLightSourceY3.Value = 200;
            myLightSourceZ3.Value = -500;

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

            btAdd.Click += new RoutedEventHandler(btAdd_Click);

            cbLOD.Items.Add(Partition.LOD.LOW);
            cbLOD.Items.Add(Partition.LOD.MEDIUM);
            cbLOD.Items.Add(Partition.LOD.HIGH);
            cbLOD.SelectionChanged += new SelectionChangedEventHandler(cbLOD_SelectionChanged);
        }

        void cbLOD_SelectionChanged(object sender, SelectionChangedEventArgs e)
        {
            scene.LOD = (Partition.LOD)e.AddedItems[0];
        }

        void btAdd_Click(object sender, RoutedEventArgs e)
        {
            scene.sceneModel.MyBlock = scene.sceneModel.MyBlock + 1;
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
            scene.sceneModel.xLightSource1.Z = (float)e.NewValue;
        }

        void myLightSourceY_ValueChanged(object sender, MySliderControl.ValueChangedEventArgs e)
        {
            scene.sceneModel.xLightSource1.Y = (float)e.NewValue;
        }

        void myLightSourceX_ValueChanged(object sender, MySliderControl.ValueChangedEventArgs e)
        {
            scene.sceneModel.xLightSource1.X = (float)e.NewValue;
        }

        void myLightSourceZ2_ValueChanged(object sender, MySliderControl.ValueChangedEventArgs e)
        {
            scene.sceneModel.xLightSource2.Z = (float)e.NewValue;
        }

        void myLightSourceY2_ValueChanged(object sender, MySliderControl.ValueChangedEventArgs e)
        {
            scene.sceneModel.xLightSource2.Y = (float)e.NewValue;
        }

        void myLightSourceX2_ValueChanged(object sender, MySliderControl.ValueChangedEventArgs e)
        {
            scene.sceneModel.xLightSource2.X = (float)e.NewValue;
        }

        void myLightSourceZ3_ValueChanged(object sender, MySliderControl.ValueChangedEventArgs e)
        {
            scene.sceneModel.xLightSource3.Z = (float)e.NewValue;
        }

        void myLightSourceY3_ValueChanged(object sender, MySliderControl.ValueChangedEventArgs e)
        {
            scene.sceneModel.xLightSource3.Y = (float)e.NewValue;
        }

        void myLightSourceX3_ValueChanged(object sender, MySliderControl.ValueChangedEventArgs e)
        {
            scene.sceneModel.xLightSource3.X = (float)e.NewValue;
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
                    CameraMovements cm = new CameraMovements();
                    cm.OnTickProcess = () =>
                    {
                        cm.Move2(scene.CameraPosition, scene.CameraTarget, 50f, _3DPresentation.CameraMovements.MOVE.FORWARD);
                        scene.CameraPosition = CameraMovements.CameraResult;
                        scene.CameraTarget = CameraMovements.LookAtResult;
                        scene.UpdateView2();
                    };
                    cm.AnimationSurface(250);
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
                    CameraMovements cm = new CameraMovements();
                    cm.OnTickProcess = () =>
                    {
                        cm.Move2(scene.CameraPosition, scene.CameraTarget, 50f, _3DPresentation.CameraMovements.MOVE.BACK);
                        scene.CameraPosition = CameraMovements.CameraResult;
                        scene.CameraTarget = CameraMovements.LookAtResult;
                        scene.UpdateView2();
                    };
                    cm.AnimationSurface(250);
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
                    CameraMovements cm = new CameraMovements();
                    cm.OnTickProcess = () =>
                    {
                        cm.Move2(scene.CameraPosition, scene.CameraTarget, 50f, _3DPresentation.CameraMovements.MOVE.LEFT);
                        scene.CameraPosition = CameraMovements.CameraResult;
                        scene.CameraTarget = CameraMovements.LookAtResult;
                        scene.UpdateView2();
                    };
                    cm.AnimationSurface(250);
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
                    CameraMovements cm = new CameraMovements();
                    cm.OnTickProcess = () =>
                    {
                        cm.Move2(scene.CameraPosition, scene.CameraTarget, 50f, _3DPresentation.CameraMovements.MOVE.RIGHT);
                        scene.CameraPosition = CameraMovements.CameraResult;
                        scene.CameraTarget = CameraMovements.LookAtResult;
                        scene.UpdateView2();
                    };
                    cm.AnimationSurface(250);
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
                    CameraMovements cm = new CameraMovements();
                    cm.OnTickProcess = () =>
                    {
                        cm.Rotate2(-8f, 0, 0, scene.CameraPosition, scene.CameraTarget);
                        scene.CameraTarget = CameraMovements.LookAtResult;
                        scene.UpdateView2();
                    };
                    cm.AnimationSurface(250);
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
                    CameraMovements cm = new CameraMovements();
                    cm.OnTickProcess = () =>
                    {
                        cm.Rotate2(8f, 0, 0, scene.CameraPosition, scene.CameraTarget);
                        scene.CameraTarget = CameraMovements.LookAtResult;
                        scene.UpdateView2();
                    };
                    cm.AnimationSurface(250);
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

                CameraMovements.RotateByMouse(new Microsoft.Xna.Framework.Vector2((float)(newPoint.Y - oldPoint.Y), (float)(newPoint.X - oldPoint.X)), scene.CameraPosition, scene.CameraTarget);
                scene.CameraTarget = CameraMovements.LookAtResult;
                scene.UpdateView2();

                oldPoint = newPoint;
            }
        }
        #endregion

        private void LayoutRoot_KeyDown(object sender, KeyEventArgs e)
        {
            if (e.Key == Key.A)
            {
                MoveLeft_Click(this, new RoutedEventArgs());
            }

            if (e.Key == Key.D)
            {
                MoveRight_Click(this, new RoutedEventArgs());
            }

            if (e.Key == Key.W)
            {
                MoveForward_Click(this, new RoutedEventArgs());
            }

            if (e.Key == Key.S)
            {
                MoveBack_Click(this, new RoutedEventArgs());
            }
        }
    }
}
