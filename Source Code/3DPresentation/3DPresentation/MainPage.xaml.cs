using System.Windows.Controls;
using System;
using System.Windows;
using Microsoft.Xna.Framework;
using System.Windows.Input;
using System.Windows.Media;
using _3DPresentation.Models;
using _3DPresentation.Controllers;
using System.IO;
using System.Collections.Generic;

namespace _3DPresentation
{
    public partial class MainPage : UserControl
    {
        private static int MAX_FRAME_RATE = 24;
        // init the 3D scene
        Scene scene = new Scene();
        MyModel model1;
        MyModel model2;
        Controller controller;

        Microsoft.Xna.Framework.Matrix model1Matrix;
        Microsoft.Xna.Framework.Matrix model2Matrix;
        public MainPage()
        {
            InitializeComponent();
            //Timeline.DesiredFrameRateProperty.OverrideMetadata(typeof(Timeline), new FrameworkPropertyMetadata { DefaultValue = 24 });
            // INGNORED
            App.Current.Host.Settings.MaxFrameRate = MAX_FRAME_RATE;

            //======== Add Models to Scene ===============================================
            model1 = scene.AddMyModel("SampleData/Data5/image_RGB_000004.png", "SampleData/Data5/image_depth_000004.dat", new Vector3(-500, 0, 0));
            model2 = scene.AddMyModel("SampleData/Data5/image_RGB_000005.png", "SampleData/Data5/image_depth_000005.dat", new Vector3(500, 0, 0));
            Microsoft.Xna.Framework.Matrix rotateMatrix = Microsoft.Xna.Framework.Matrix.CreateRotationY((122.0f * 3.14f / 180.0f));
            model2.WorldMatrix *= rotateMatrix;
            rotateMatrix = Microsoft.Xna.Framework.Matrix.CreateRotationX((122.0f * 3.14f / 180.0f));
            model2.WorldMatrix *= rotateMatrix;
            rotateMatrix = Microsoft.Xna.Framework.Matrix.CreateRotationZ((122.0f * 3.14f / 180.0f));
            model2.WorldMatrix *= rotateMatrix;                       
            model1Matrix = model1.WorldMatrix;
            model2Matrix = model2.WorldMatrix;

            scene.AddSimpleModel(CreateAxisModel(), Vector3.Zero);
            light1 = scene.AddLightPoint(new Vector3(0, 0, 0), GlobalVars.White, 5000);
            light2 = scene.AddLightPoint(new Vector3(0, 0, 0), GlobalVars.White, 5000);
            light3 = scene.AddLightPoint(new Vector3(0, 0, 0), GlobalVars.White, 5000);
            light1.Model.IsVisible = false;
            light2.Model.IsVisible = false;
            light3.Model.IsVisible = false;

            btAnimate.Click += new RoutedEventHandler(btAnimate_Click);
            btNext.Click += new RoutedEventHandler(btNext_Click);            
            btReset.Click += new RoutedEventHandler(btReset_Click);
            chkModel1.Checked += new RoutedEventHandler(chkModel1_Checked);
            chkModel1.Unchecked += new RoutedEventHandler(chkModel1_Unchecked);
            chkModel2.Checked += new RoutedEventHandler(chkModel2_Checked);
            chkModel2.Unchecked += new RoutedEventHandler(chkModel2_Unchecked);
            myOpenFile.FileOpened += new OpenFileControl.FileOpenedHandler(myOpenFile_FileOpened);
            myWriteFile.FileOpened += new OpenFileControl.FileOpenedHandler(myWriteFile_FileOpened);
            //============================================================================

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

            //============== Set Collapse ======================
            myLightSourceX.Visibility = System.Windows.Visibility.Collapsed;
            myLightSourceY.Visibility = System.Windows.Visibility.Collapsed;
            myLightSourceZ.Visibility = System.Windows.Visibility.Collapsed;
            myLightSourceX2.Visibility = System.Windows.Visibility.Collapsed;
            myLightSourceY2.Visibility = System.Windows.Visibility.Collapsed;
            myLightSourceZ2.Visibility = System.Windows.Visibility.Collapsed; 
            myLightSourceX3.Visibility = System.Windows.Visibility.Collapsed;
            myLightSourceY3.Visibility = System.Windows.Visibility.Collapsed;
            myLightSourceZ3.Visibility = System.Windows.Visibility.Collapsed;
            myLightIntensity.Visibility = System.Windows.Visibility.Collapsed;
            myAmbientIntensity.Visibility = System.Windows.Visibility.Collapsed;
            //==================================================
            CompositionTarget.Rendering += new EventHandler(CompositionTarget_Rendering);

            myUDRMZControl.MoveForwardClick += new RoutedEventHandler(MoveForward_Click);
            myUDRMZControl.MoveBackClick += new RoutedEventHandler(MoveBack_Click);
            myUDRMZControl.MoveLeftClick += new RoutedEventHandler(MoveLeft_Click);
            myUDRMZControl.MoveRightClick += new RoutedEventHandler(MoveRight_Click);

            myUDRMZControl.RotateLeftClick += new RoutedEventHandler(RotateLeft_Click);
            myUDRMZControl.RotateRightClick += new RoutedEventHandler(RotateRight_Click);

            myUDRMZControl.RotateUpClick += new RoutedEventHandler(RotateUp_Click);
            myUDRMZControl.RotateDownClick += new RoutedEventHandler(RotateDown_Click);

            cbLOD.Items.Add(GlobalVars.LOD.LOW);
            cbLOD.Items.Add(GlobalVars.LOD.MEDIUM);
            cbLOD.Items.Add(GlobalVars.LOD.HIGH);
            cbLOD.SelectionChanged += new SelectionChangedEventHandler(cbLOD_SelectionChanged);

            drawingSurface.Draw += new EventHandler<DrawEventArgs>(drawingSurface_Draw);
            drawingSurface.SizeChanged += new SizeChangedEventHandler(drawingSurface_SizeChanged);
        }

        void myWriteFile_FileOpened(object sender, OpenFileControl.FileOpenedEventArgs e)
        {
            controller.ExportMergedMesh(e.FileInfo);
        }

        void myOpenFile_FileOpened(object sender, OpenFileControl.FileOpenedEventArgs e)
        {
            controller = new Controller(model1, model2, e.FileInfo);
        }

        void chkModel2_Unchecked(object sender, RoutedEventArgs e)
        {
            model2.IsVisible = false;
        }

        void chkModel2_Checked(object sender, RoutedEventArgs e)
        {
            model2.IsVisible = true;
        }

        void chkModel1_Unchecked(object sender, RoutedEventArgs e)
        {
            model1.IsVisible = false;
        }

        void chkModel1_Checked(object sender, RoutedEventArgs e)
        {
            model1.IsVisible = true;
        }        

        void btReset_Click(object sender, RoutedEventArgs e)
        {
            model1.WorldMatrix = model1Matrix;
            model2.WorldMatrix = model2Matrix;
            controller.Reset();            
        }

        void btNext_Click(object sender, RoutedEventArgs e)
        {
            controller.isEnable = true;
        }

        void btAnimate_Click(object sender, RoutedEventArgs e)
        {
            controller.Run();
        }

        void drawingSurface_SizeChanged(object sender, SizeChangedEventArgs e)
        {
            scene.Scene_SizeChanged(sender, e);
        }

        void drawingSurface_Draw(object sender, DrawEventArgs e)
        {
            if (isDraw)
            {
                scene.Scene_Draw(sender, e);                
            }
            e.InvalidateSurface();
        }

        LightPoint light1;
        LightPoint light2;
        LightPoint light3;

        private VertexPositionColor[] CreateAxisModel()
        {
            VertexPositionColor[] vertices = new VertexPositionColor[6];
            vertices[0] = new VertexPositionColor(new Vector3(-3000, 0, 0), GlobalVars.Red);
            vertices[1] = new VertexPositionColor(new Vector3(+3000, 0, 0), GlobalVars.White);

            vertices[2] = new VertexPositionColor(new Vector3(0, -3000, 0), GlobalVars.Green);
            vertices[3] = new VertexPositionColor(new Vector3(0, 3000, 0), GlobalVars.White);

            vertices[4] = new VertexPositionColor(new Vector3(0, 0, -3000), GlobalVars.Blue);
            vertices[5] = new VertexPositionColor(new Vector3(0, 0, 3000), GlobalVars.White);
            return vertices;
        }

        void cbLOD_SelectionChanged(object sender, SelectionChangedEventArgs e)
        {
            scene.LOD = (_3DPresentation.GlobalVars.LOD)e.AddedItems[0];
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
            myDrawFPS.Dispatcher.BeginInvoke(new Action(() => { myDrawFPS.Text = "DrawFPS : " + scene.FPS; }));
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
            light1.Position = new Vector3(light1.Position.X, light1.Position.Y, (float)e.NewValue);
        }

        void myLightSourceY_ValueChanged(object sender, MySliderControl.ValueChangedEventArgs e)
        {
            light1.Position = new Vector3(light1.Position.X, (float)e.NewValue, light1.Position.Z);
        }

        void myLightSourceX_ValueChanged(object sender, MySliderControl.ValueChangedEventArgs e)
        {
            light1.Position = new Vector3((float)e.NewValue, light1.Position.Y, light1.Position.Z);
        }

        void myLightSourceZ2_ValueChanged(object sender, MySliderControl.ValueChangedEventArgs e)
        {
            light2.Position = new Vector3(light2.Position.X, light2.Position.Y, (float)e.NewValue); ;
        }

        void myLightSourceY2_ValueChanged(object sender, MySliderControl.ValueChangedEventArgs e)
        {
            light2.Position = new Vector3(light2.Position.X, (float)e.NewValue, light2.Position.Z);
        }

        void myLightSourceX2_ValueChanged(object sender, MySliderControl.ValueChangedEventArgs e)
        {
            light2.Position = new Vector3((float)e.NewValue, light2.Position.Y, light2.Position.Z);
        }

        void myLightSourceZ3_ValueChanged(object sender, MySliderControl.ValueChangedEventArgs e)
        {
            light3.Position = new Vector3(light3.Position.X, light3.Position.Y, (float)e.NewValue);
        }

        void myLightSourceY3_ValueChanged(object sender, MySliderControl.ValueChangedEventArgs e)
        {
            light3.Position = new Vector3(light3.Position.X, (float)e.NewValue, light3.Position.Z);
        }

        void myLightSourceX3_ValueChanged(object sender, MySliderControl.ValueChangedEventArgs e)
        {
            light3.Position = new Vector3((float)e.NewValue, light3.Position.Y, light3.Position.Z);
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
                scene.CameraPosition = new Vector3(scene.CameraPosition.X, scene.CameraPosition.Y + 10, scene.CameraPosition.Z);
                scene.UpdateView2();
                //MoveForward_Click(this, new RoutedEventArgs());
            }

            if (e.Key == Key.S)
            {
                scene.CameraPosition = new Vector3(scene.CameraPosition.X, scene.CameraPosition.Y - 10, scene.CameraPosition.Z);
                scene.UpdateView2();
                //MoveBack_Click(this, new RoutedEventArgs());
            }
        }
    }
}
