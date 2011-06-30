using System.Net;
using System.Reflection;
using System.Runtime.InteropServices.Automation;
using System.Threading;
using System.Windows.Controls;
using System;
using System.Windows;
using System.Windows.Media.Imaging;
using Microsoft.Xna.Framework;
using System.Windows.Input;
using System.Windows.Media;
using SharpGIS;
using _3DPresentation.Models;
using System.IO;
using System.Collections.Generic;

namespace _3DPresentation
{
    public partial class MainPage : UserControl
    {
        private static int MAX_FRAME_RATE = 24;
        // init the 3D scene
        Scene scene = new Scene();
        private string _strWorkingDirectory;
        private string _strWorkingDirectoryTemp;

        public MainPage()
        {
            InitializeComponent();
            //Timeline.DesiredFrameRateProperty.OverrideMetadata(typeof(Timeline), new FrameworkPropertyMetadata { DefaultValue = 24 });
            // INGNORED
            App.Current.Host.Settings.MaxFrameRate = MAX_FRAME_RATE;

            //======== Add Models to Scene ===============================================
            scene.AddSimpleModel(CreateAxisModel(), Vector3.Zero);            
            //============================================================================           
            CompositionTarget.Rendering += new EventHandler(CompositionTarget_Rendering);

            openFile.Label = "PointCloud...";
            openFile2.Label = "Model...";

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
        const float ForwardSpeed = 100.0f;
        const float BackSpeed = 100.0f;
        const float LeftSpeed = 100.0f;
        const float RightSpeed = 100.0f;

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

        private void LayoutRoot_KeyDown(object sender, KeyEventArgs e)
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

                using (dynamic shell = AutomationFactory.CreateObject("WScript.Shell"))
                {
                    //player d:\\test2 d:\\grab1 d:\\kineck_calibration.yml
                    string strQuery =
                    string.Format("{0} {1} {2} {3} {4}",
                                  WorkingDirectory + "\\recontructor\\rgbd-reconstructor.exe",
                                  "player",
                                  WorkingDirectory + "\\result",
                                  WorkingDirectory + "\\recorded\\grab1",
                                  WorkingDirectory + "\\recontructor\\kineck_calibration.yml");
                    shell.Run(strQuery);
                }

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
                                            if (fi.Name.StartsWith("DecreaseSameVertex"))
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
