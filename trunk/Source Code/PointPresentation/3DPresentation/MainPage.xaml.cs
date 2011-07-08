using System;
using System.IO;
using System.Collections.Generic;
using System.Net;
using System.Reflection;
using System.Runtime.InteropServices.Automation;
using System.Threading;
using System.Windows.Controls;
using System.Windows;
using System.Windows.Media.Imaging;
using Microsoft.Xna.Framework;
using System.Windows.Input;
using SharpGIS;
using ShaderEffectsLibrary;


namespace _3DPresentation
{
    public partial class MainPage : UserControl
    {
        private static int MAX_FRAME_RATE = 24;
        // init the 3D scene
        Scene scene = new Scene();
        private string _strWorkingDirectory;
        private string _strWorkingDirectoryTemp;

        TransitionEffect transitionEffect;
        BitmapImage bitmapImage;
        private void BeginAnimation()
        {
            WriteableBitmap capture = new WriteableBitmap(image, new System.Windows.Media.ScaleTransform());
            System.Windows.Media.ImageBrush imageBrush = new System.Windows.Media.ImageBrush();
            imageBrush.ImageSource = capture;
            transitionEffect.OldImage = imageBrush;

            //image.Source = getNextBitmapImage();
            //image.Effect = transitionEffect;
            button1.Effect = transitionEffect;

            #region WPF ShaderEffect Animation
            /*
            DoubleAnimation da = new DoubleAnimation();
            da.From = 0;
            da.To = 1;
            da.Duration = TimeSpan.FromSeconds(3);
            //da.AutoReverse = true;
            //da.RepeatBehavior = RepeatBehavior.Forever;
            transitionEffect.BeginAnimation(TransitionEffect.ProgressProperty, da);
             * */
            #endregion

            #region Silverlight ShaderEffect Animation

            System.Windows.Media.Animation.DoubleAnimation da = new System.Windows.Media.Animation.DoubleAnimation();
            da.From = 0;
            da.To = 1;
            da.Duration = TimeSpan.FromSeconds(3);
            da.AutoReverse = true;
            //da.RepeatBehavior = System.Windows.Media.Animation.RepeatBehavior.Forever;

            //Storyboard st = (LayoutRoot.Resources)["st"] as Storyboard;
            System.Windows.Media.Animation.Storyboard st = new System.Windows.Media.Animation.Storyboard();
            System.Windows.Media.Animation.Storyboard.SetTarget(da, transitionEffect);
            System.Windows.Media.Animation.Storyboard.SetTargetProperty(da, new PropertyPath(TransitionEffect.ProgressProperty));
            st.Children.Add(da);
            st.Begin();
            
            #endregion
        }
        public MainPage()
        {
            transitionEffect = new CircleRevealTransition();
            bitmapImage = new BitmapImage(_3DPresentation.Utils.Global.MakePackUri("Images/3.jpg")); 

            InitializeComponent();
            //Timeline.DesiredFrameRateProperty.OverrideMetadata(typeof(Timeline), new FrameworkPropertyMetadata { DefaultValue = 24 });
            // INGNORED
            App.Current.Host.Settings.MaxFrameRate = MAX_FRAME_RATE;

            //======== Add Models to Scene ===============================================
            scene.AddSimpleModel(CreateAxisModel(), Vector3.Zero);            
            //============================================================================           
            System.Windows.Media.CompositionTarget.Rendering += new EventHandler(CompositionTarget_Rendering);

            openFile.Label = "PointCloud...";
            openFile2.Label = "Model...";
            openFile3.Label = "Light...";

            myUDRMZControl.MoveForwardClick += new RoutedEventHandler(MoveForward_Click);
            myUDRMZControl.MoveBackClick += new RoutedEventHandler(MoveBack_Click);
            myUDRMZControl.MoveLeftClick += new RoutedEventHandler(MoveLeft_Click);
            myUDRMZControl.MoveRightClick += new RoutedEventHandler(MoveRight_Click);

            myUDRMZControl.RotateLeftClick += new RoutedEventHandler(RotateLeft_Click);
            myUDRMZControl.RotateRightClick += new RoutedEventHandler(RotateRight_Click);

            myUDRMZControl.RotateUpClick += new RoutedEventHandler(RotateUp_Click);
            myUDRMZControl.RotateDownClick += new RoutedEventHandler(RotateDown_Click);

            openFile.FileOpened += new OpenFileControl.FileOpenedHandler(openFile_FileOpened);
            openFile2.FileOpened += new OpenFileControl.FileOpenedHandler(openFile2_FileOpened);
            openFile3.FileOpened += new OpenFileControl.FileOpenedHandler(openFile3_FileOpened);

            drawingSurface.Draw += new EventHandler<DrawEventArgs>(drawingSurface_Draw);
            drawingSurface.SizeChanged += new SizeChangedEventHandler(drawingSurface_SizeChanged);
        }

        public string WorkingDirectory
        {
            get { return _strWorkingDirectory; }
            set { _strWorkingDirectory = value;
                WorkingDirectoryTemp = _strWorkingDirectory + "\\temp";
            }
        }

        public string WorkingDirectoryTemp
        {
            get { return _strWorkingDirectoryTemp; }
            set { _strWorkingDirectoryTemp = value; }
        }

        void openFile3_FileOpened(object sender, OpenFileControl.FileOpenedEventArgs e)
        {
            Models.FaceModel.FaceModel light = scene.AddLightModel(e.FileInfo);
            light.WorldMatrix *= Matrix.CreateTranslation(GlobalVars.Light1);
            light.WorldMatrix *= Matrix.CreateScale(1000.0f);
        }

        void openFile2_FileOpened(object sender, OpenFileControl.FileOpenedEventArgs e)
        {
            scene.AddFaceModel(e.FileInfo);
        }

        void openFile_FileOpened(object sender, OpenFileControl.FileOpenedEventArgs e)
        {
            scene.AddPointModel(e.FileInfo);
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
            //myUIFPS.Dispatcher.BeginInvoke(new Action(() => { myUIFPS.Text = "UIFPS : " + uiFPS; }));
            myDrawFPS.Dispatcher.BeginInvoke(new Action(() => { myDrawFPS.Text = "DrawFPS : " + scene.FPS; }));
        }

        bool isDraw = false;
        bool isStart = false;
        private void button1_Click(object sender, RoutedEventArgs e)
        {
            BeginAnimation();
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
        const float ForwardSpeed = 0.1f;
        const float BackSpeed = 0.1f;
        const float LeftSpeed = 0.01f;//100.0f;
        const float RightSpeed = 0.1f;

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
                        cm.Move2(scene.CameraPosition, scene.CameraTarget, ForwardSpeed, _3DPresentation.CameraMovements.MOVE.FORWARD);
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
                        cm.Move2(scene.CameraPosition, scene.CameraTarget, BackSpeed, _3DPresentation.CameraMovements.MOVE.BACK);
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
                        cm.Move2(scene.CameraPosition, scene.CameraTarget, LeftSpeed, _3DPresentation.CameraMovements.MOVE.LEFT);
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
                        cm.Move2(scene.CameraPosition, scene.CameraTarget, RightSpeed, _3DPresentation.CameraMovements.MOVE.RIGHT);
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

        int controlLight = 0;
        private void LayoutRoot_KeyDown(object sender, KeyEventArgs e)
        {            
            if (e.Key == Key.NumPad1)
            {
                GlobalVars.EnableLights = new Vector4(1.0f, GlobalVars.EnableLights.Y, GlobalVars.EnableLights.Z, GlobalVars.EnableLights.W);
                controlLight = 1;
            }
            if (e.Key == Key.NumPad2)
            {
                GlobalVars.EnableLights = new Vector4(GlobalVars.EnableLights.X, 1.0f, GlobalVars.EnableLights.Z, GlobalVars.EnableLights.W);
                controlLight = 2;
            }
            if (e.Key == Key.NumPad3)
            {
                GlobalVars.EnableLights = new Vector4(GlobalVars.EnableLights.X, GlobalVars.EnableLights.Y, 1.0f, GlobalVars.EnableLights.W);
                controlLight = 3;
            }
            if (e.Key == Key.NumPad4)
            {
                GlobalVars.EnableLights = new Vector4(GlobalVars.EnableLights.X, GlobalVars.EnableLights.Y, GlobalVars.EnableLights.Z, 1.0f);
                controlLight = 4;
            }

            if (controlLight == 1)
            {
                if (e.Key == Key.A)
                {
                    GlobalVars.Light1 = new Vector3(GlobalVars.Light1.X - LeftSpeed, GlobalVars.Light1.Y, GlobalVars.Light1.Z);
                    //MoveLeft_Click(this, new RoutedEventArgs());
                }

                if (e.Key == Key.D)
                {
                    GlobalVars.Light1 = new Vector3(GlobalVars.Light1.X + LeftSpeed, GlobalVars.Light1.Y, GlobalVars.Light1.Z);
                    //MoveRight_Click(this, new RoutedEventArgs());
                }

                if (e.Key == Key.W)
                {
                    GlobalVars.Light1 = new Vector3(GlobalVars.Light1.X, GlobalVars.Light1.Y + LeftSpeed, GlobalVars.Light1.Z);
                    //scene.CameraPosition = new Vector3(scene.CameraPosition.X, scene.CameraPosition.Y + 10, scene.CameraPosition.Z);
                    //scene.UpdateView2();
                    //MoveForward_Click(this, new RoutedEventArgs());
                }

                if (e.Key == Key.S)
                {
                    GlobalVars.Light1 = new Vector3(GlobalVars.Light1.X, GlobalVars.Light1.Y - LeftSpeed, GlobalVars.Light1.Z);
                    //scene.CameraPosition = new Vector3(scene.CameraPosition.X, scene.CameraPosition.Y - 10, scene.CameraPosition.Z);
                    //scene.UpdateView2();
                    //MoveBack_Click(this, new RoutedEventArgs());
                }

                if (e.Key == Key.Q)
                {
                    GlobalVars.Light1 = new Vector3(GlobalVars.Light1.X, GlobalVars.Light1.Y, GlobalVars.Light1.Z - LeftSpeed);
                }

                if (e.Key == Key.E)
                {
                    GlobalVars.Light1 = new Vector3(GlobalVars.Light1.X, GlobalVars.Light1.Y, GlobalVars.Light1.Z + LeftSpeed);
                }
            }

            if (controlLight == 2)
            {
                if (e.Key == Key.A)
                {
                    GlobalVars.Light2 = new Vector3(GlobalVars.Light2.X - LeftSpeed, GlobalVars.Light2.Y, GlobalVars.Light2.Z);
                    //MoveLeft_Click(this, new RoutedEventArgs());
                }

                if (e.Key == Key.D)
                {
                    GlobalVars.Light2 = new Vector3(GlobalVars.Light2.X + LeftSpeed, GlobalVars.Light2.Y, GlobalVars.Light2.Z);
                    //MoveRight_Click(this, new RoutedEventArgs());
                }

                if (e.Key == Key.W)
                {
                    GlobalVars.Light2 = new Vector3(GlobalVars.Light2.X, GlobalVars.Light2.Y + LeftSpeed, GlobalVars.Light2.Z);
                    //scene.CameraPosition = new Vector3(scene.CameraPosition.X, scene.CameraPosition.Y + 10, scene.CameraPosition.Z);
                    //scene.UpdateView2();
                    //MoveForward_Click(this, new RoutedEventArgs());
                }

                if (e.Key == Key.S)
                {
                    GlobalVars.Light2 = new Vector3(GlobalVars.Light2.X, GlobalVars.Light2.Y - LeftSpeed, GlobalVars.Light2.Z);
                    //scene.CameraPosition = new Vector3(scene.CameraPosition.X, scene.CameraPosition.Y - 10, scene.CameraPosition.Z);
                    //scene.UpdateView2();
                    //MoveBack_Click(this, new RoutedEventArgs());
                }

                if (e.Key == Key.Q)
                {
                    GlobalVars.Light2 = new Vector3(GlobalVars.Light2.X, GlobalVars.Light2.Y, GlobalVars.Light2.Z - LeftSpeed);
                }

                if (e.Key == Key.E)
                {
                    GlobalVars.Light2 = new Vector3(GlobalVars.Light2.X, GlobalVars.Light2.Y, GlobalVars.Light2.Z + LeftSpeed);
                }
            }

            if (controlLight == 3)
            {
                if (e.Key == Key.A)
                {
                    GlobalVars.Light3 = new Vector3(GlobalVars.Light3.X - LeftSpeed, GlobalVars.Light3.Y, GlobalVars.Light3.Z);
                    //MoveLeft_Click(this, new RoutedEventArgs());
                }

                if (e.Key == Key.D)
                {
                    GlobalVars.Light3 = new Vector3(GlobalVars.Light3.X + LeftSpeed, GlobalVars.Light3.Y, GlobalVars.Light3.Z);
                    //MoveRight_Click(this, new RoutedEventArgs());
                }

                if (e.Key == Key.W)
                {
                    GlobalVars.Light3 = new Vector3(GlobalVars.Light3.X, GlobalVars.Light3.Y + LeftSpeed, GlobalVars.Light3.Z);
                    //scene.CameraPosition = new Vector3(scene.CameraPosition.X, scene.CameraPosition.Y + 10, scene.CameraPosition.Z);
                    //scene.UpdateView2();
                    //MoveForward_Click(this, new RoutedEventArgs());
                }

                if (e.Key == Key.S)
                {
                    GlobalVars.Light3 = new Vector3(GlobalVars.Light3.X, GlobalVars.Light3.Y - LeftSpeed, GlobalVars.Light3.Z);
                    //scene.CameraPosition = new Vector3(scene.CameraPosition.X, scene.CameraPosition.Y - 10, scene.CameraPosition.Z);
                    //scene.UpdateView2();
                    //MoveBack_Click(this, new RoutedEventArgs());
                }

                if (e.Key == Key.Q)
                {
                    GlobalVars.Light3 = new Vector3(GlobalVars.Light3.X, GlobalVars.Light3.Y, GlobalVars.Light3.Z - LeftSpeed);
                }

                if (e.Key == Key.E)
                {
                    GlobalVars.Light3 = new Vector3(GlobalVars.Light3.X, GlobalVars.Light3.Y, GlobalVars.Light3.Z + LeftSpeed);
                }
            }

            if (controlLight == 4)
            {
                if (e.Key == Key.A)
                {
                    GlobalVars.Light4 = new Vector3(GlobalVars.Light4.X - LeftSpeed, GlobalVars.Light4.Y, GlobalVars.Light4.Z);
                    //MoveLeft_Click(this, new RoutedEventArgs());
                }

                if (e.Key == Key.D)
                {
                    GlobalVars.Light4 = new Vector3(GlobalVars.Light4.X + LeftSpeed, GlobalVars.Light4.Y, GlobalVars.Light4.Z);
                    //MoveRight_Click(this, new RoutedEventArgs());
                }

                if (e.Key == Key.W)
                {
                    GlobalVars.Light4 = new Vector3(GlobalVars.Light4.X, GlobalVars.Light4.Y + LeftSpeed, GlobalVars.Light4.Z);
                    //scene.CameraPosition = new Vector3(scene.CameraPosition.X, scene.CameraPosition.Y + 10, scene.CameraPosition.Z);
                    //scene.UpdateView2();
                    //MoveForward_Click(this, new RoutedEventArgs());
                }

                if (e.Key == Key.S)
                {
                    GlobalVars.Light4 = new Vector3(GlobalVars.Light4.X, GlobalVars.Light4.Y - LeftSpeed, GlobalVars.Light4.Z);
                    //scene.CameraPosition = new Vector3(scene.CameraPosition.X, scene.CameraPosition.Y - 10, scene.CameraPosition.Z);
                    //scene.UpdateView2();
                    //MoveBack_Click(this, new RoutedEventArgs());
                }

                if (e.Key == Key.Q)
                {
                    GlobalVars.Light4 = new Vector3(GlobalVars.Light4.X, GlobalVars.Light4.Y, GlobalVars.Light4.Z - LeftSpeed);
                }

                if (e.Key == Key.E)
                {
                    GlobalVars.Light4 = new Vector3(GlobalVars.Light4.X, GlobalVars.Light4.Y, GlobalVars.Light4.Z + LeftSpeed);
                }
            }
            myUIFPS.Dispatcher.BeginInvoke(new Action(() => { myUIFPS.Text = "Light 1: " + GlobalVars.Light1.X.ToString("0.00") + " " + GlobalVars.Light1.Y.ToString("0.00") + " " + GlobalVars.Light1.Z.ToString("0.00"); }));
        }

        void SetupWorkingDirectory()
        {
            WorkingDirectory = "d:\\\\test2";

        }

        private void Button_Click(object sender, RoutedEventArgs e)
        {
            try
            {
                SetupWorkingDirectory();

                //using (dynamic shell = AutomationFactory.CreateObject("WScript.Shell"))
                //{
                //    //player d:\\test2 d:\\grab1 d:\\kineck_calibration.yml
                //    string strQuery =
                //    string.Format("{0} {1} {2} {3} {4}",
                //                  WorkingDirectory + "\\recontructor\\rgbd-reconstructor.exe",
                //                  "player",
                //                  WorkingDirectory + "\\result",
                //                  WorkingDirectory + "\\recorded\\grab3",
                //                  WorkingDirectory + "\\recontructor\\kineck_calibration.yml");
                //    shell.Run(strQuery);
                //}

                new Thread(() =>
                {
                    try
                    {
                        using (dynamic SWbemLocator = AutomationFactory.CreateObject("WbemScripting.SWbemLocator"))
                        {
                            SWbemLocator.Security_.ImpersonationLevel = 3;
                            SWbemLocator.Security_.AuthenticationLevel = 4;
                            dynamic IService = SWbemLocator.ConnectServer(".", @"root\cimv2");

                            string strWatchFolder = (WorkingDirectory + "\\result").Replace(@"\", @"\\\\").Replace(@"\\\\\\\\", @"\\\\");
                            //string strWatchFolder = (@"d:\\\\test2\\\\result");//.Replace(@"\", @"\\");

                            string fileSystemWatcherQuery =
                                string.Format(@"SELECT * FROM __InstanceOperationEvent WITHIN 3 WHERE Targetinstance ISA 'CIM_DirectoryContainsFile' and TargetInstance.GroupComponent= 'Win32_Directory.Name=""{0}""'",
                                strWatchFolder);
                            dynamic monitor = IService.ExecNotificationQuery(fileSystemWatcherQuery);

                            //Dispatcher.BeginInvoke(() => MessageBox.Show(@"Now listening to file changes on d:\test2"));

                            while (true)
                            {
                                dynamic eventObject = monitor.NextEvent();
                                string eventType = eventObject.Path_.Class;
                                string path = eventObject.TargetInstance.PartComponent;

                                Dispatcher.BeginInvoke(() =>
                                {
                                    //MessageBox.Show(eventType + ": " + path);
                                    string[] strSplit = path.Split('\"');
                                    //MessageBox.Show(eventType + ": " + strSplit[strSplit.Length - 2]);
                                    string strFileName = strSplit[strSplit.Length - 2];
                                    if (eventType.IndexOf("CreationEvent") > 0)
                                    {
                                        //create event
                                        //MessageBox.Show("Create" + ": " + strFileName);

                                        //BitmapImage bi = new BitmapImage();
                                        //FileInfo fio = new FileInfo(strFileName);
                                        //System.IO.Stream stream2 = fio.OpenRead();
                                        //bi.SetSource(stream2);
                                        //myImage.Source = bi;
                                        //stream2.Close();
                                        FileInfo fi = new FileInfo(strFileName);
                                        if (fi.Extension.Equals(".ply"))
                                        {
                                            if (fi.Name.StartsWith("NotDecreaseSameVertex"))
                                            {
                                                scene.AddPointModel(fi);
                                            }

                                        }

                                        return;
                                    }

                                    if (eventType.IndexOf("DeletionEvent") > 0)
                                    {
                                        //delete event
                                        //MessageBox.Show("Delete" + ": " + strFileName);
                                        return;
                                    }
                                });
                            }
                        }
                    }
                    catch (Exception ex)
                    {
                        MessageBox.Show(ex.Message);
                        throw;
                    }
                    
                }).Start();
            }
            catch (Exception ex)
            {
                MessageBox.Show(ex.Message);
                throw;
            }
        }

        private void Button_Click_1(object sender, RoutedEventArgs e)
        {//download pakage
            try
            {
                SetupWorkingDirectory();
                ClientPackage ck = new ClientPackage();
                ck.DownloadtoClient("/recontructor.zip", WorkingDirectory);
            }
            catch (Exception ex)
            {
                MessageBox.Show(ex.Message);
                throw;
            }
        }

        private void Button_Click_2(object sender, RoutedEventArgs e)
        {//stop c++ exe
            try
            {
                string[] lines = { "exit" };
                System.IO.File.WriteAllLines(WorkingDirectoryTemp + "\\cm.txt", lines);
                ClientFileAndDirectory.MoveFile(WorkingDirectoryTemp + "\\cm.txt", WorkingDirectory + "\\result\\cm.txt");
            }
            catch (Exception ex)
            {
                MessageBox.Show(ex.Message);
                throw;
            }
            
        }
    }
}
