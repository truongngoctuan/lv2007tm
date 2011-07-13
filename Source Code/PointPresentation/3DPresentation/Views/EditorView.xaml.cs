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
using System.Windows.Navigation;
using System.Windows.Shapes;
using _3DPresentation.Views.Editor;
using System.Windows.Controls.Primitives;
using System.Threading;
using _3DPresentation.Models;
using System.Windows.Media.Imaging;
using Microsoft.Xna.Framework;
using System.IO;
using _3DPresentation.Utils;

namespace _3DPresentation
{
    public partial class EditorView : Page
    {
        #region BienDungChung
        private string _strWorkingDirectory = string.Empty;
        private string _strWorkingDirectoryTemp;

        public string WorkingDirectory
        {
            get { return _strWorkingDirectory; }
            set
            {
                _strWorkingDirectory = value;
                WorkingDirectoryTemp = _strWorkingDirectory + "\\temp";
            }
        }

        public string WorkingDirectoryTemp
        {
            get { return _strWorkingDirectoryTemp; }
            set { _strWorkingDirectoryTemp = value; }
        }

        public void SetupWorkingDirectory()
        {
            if (WorkingDirectory == string.Empty)
            {
                WorkingDirectory = "d:\\\\test2";
            }
                if (!ClientFileAndDirectory.FolderExists(WorkingDirectory)) ClientFileAndDirectory.CreateFolder(WorkingDirectory);
                if (!ClientFileAndDirectory.FolderExists(WorkingDirectoryTemp)) ClientFileAndDirectory.CreateFolder(WorkingDirectoryTemp);
                if (!ClientFileAndDirectory.FolderExists(WorkingDirectory + "\\result")) ClientFileAndDirectory.CreateFolder(WorkingDirectory + "\\result");
                if (!ClientFileAndDirectory.FolderExists(WorkingDirectory + "\\recorded")) ClientFileAndDirectory.CreateFolder(WorkingDirectory + "\\recorded");
        }
        #endregion

        private Popup simplePopup = new Popup();

        public EditorView()
        {
            InitializeComponent();

            toolbar.ParentEditor = this;
            frameViewer.ParentView = this;
            odControl.ParentEditor = this;

            ArrFrame = new List<BaseModel>();

            //BaseModel newModel = PointModel.Import(new System.IO.FileInfo("d:\\NotDecreaseSameVertex_0000.ply"));
            //vcOjectViewer.AddModel(newModel);
            //vcOjectViewer.SetTarget(newModel);

            odControl.Capture += new EventHandler(odControl_Capture);
            odControl.Record += new EventHandler(odControl_Record);
            odControl.Pause += new EventHandler(odControl_Pause);
            odControl.Resume += new EventHandler(odControl_Resume);
            odControl.Stop += new EventHandler(odControl_Stop);

            vcOjectViewer.BackgoundColor = System.Windows.Media.Color.FromArgb(0, 0, 0, 0);

        }

        // Executes when the user navigates to this page.
        protected override void OnNavigatedTo(NavigationEventArgs e)
        {
        }


        void OnImageSelected(object sender, ImageSelectedEventArgs e)
        {
            if (this.simplePopup.Child != null)
            {
                ((SimplePopupContent)this.simplePopup.Child).StopTimer();
            }
            currentImage.Source = e.Source;
            SimplePopupContent spc = new SimplePopupContent();
            spc.SelectedIndex = e.SelectedIndex;
            spc.ParentView = this;


            this.simplePopup.Child = spc;
            this.simplePopup.HorizontalOffset = frameViewer.ClickedPositionParent.X;
            this.simplePopup.VerticalOffset = frameViewer.ClickedPositionParent.Y;
            this.simplePopup.IsOpen = true;
        }

        void imageSelector_Loaded(object sender, RoutedEventArgs e)
        {

        }

        #region Popup
        public void DeleteFrame(int iIndex)
        {
            //delete
            frameViewer.DeleteImage(iIndex);
            vcOjectViewer.RemoveModel(_arrFrame[iIndex]);
            _arrFrame.RemoveAt(iIndex);
        }

        public void SetFixedImageIndex(int iIndex)
        {
            FixedImageIndex = iIndex;
        }

        public void SetReferenceImageIndex(int iIndex)
        {
            ReferenceImageIndex = iIndex;
        }

        public void ClosePopup()
        {
            this.simplePopup.IsOpen = false;
        }
        #endregion

        #region Fixed - Reference
        int iFixedImageIndex = -1;


        public int FixedImageIndex
        {
            get { return iFixedImageIndex; }
            set { iFixedImageIndex = value; }
        }
        int iReferenceImageIndex = -1;

        public int ReferenceImageIndex
        {
            get { return iReferenceImageIndex; }
            set { iReferenceImageIndex = value; }
        }
        #endregion

        #region Frame
        List<BaseModel> _arrFrame;


        public List<BaseModel> ArrFrame
        {
            get { return _arrFrame; }
            set { _arrFrame = value; }
        }

        private static object lockThis = new object();
        public void AddFrame(string strFrameName)
        {
            FileInfo fi = new System.IO.FileInfo(strFrameName);
            AddFrame(fi);
        }

        public void AddFrame(FileInfo fi)
        {
            try
            {
                lock (lockThis)
                {
                    BaseModel model = PointModel.Import(fi);
                    ArrFrame.Add(model);
                    vcOjectViewer.AddModel(ArrFrame[ArrFrame.Count - 1]);
                    if (ArrFrame.Count == 1)
                    {
                        vcOjectViewer.SetTarget(ArrFrame[ArrFrame.Count - 1]);
                    }

                    //Babylon.Toolbox.OrbitCamera cam = new Babylon.Toolbox.OrbitCamera { Alpha = (float)Math.PI / 2 };

                    ////setmodel target
                    //cam.Radius = model.BoundingInfo.BoundingSphereWorld.Radius * 4.0f;
                    //cam.Target = model.BoundingInfo.BoundingSphereWorld.Center;
                    //cam.Alpha = cam.Alpha; // to raise event => recompute Position to get new ViewMatrix

                    frameViewer.AddImage(model.toBitmap());

                    //this.currentImage.Source = model.toBitmap(300, 300, vcOjectViewer.ViewScene.Camera);
                }
            }
            catch (Exception ex)
            {
                MessageBox.Show(ex.Message);
            }
        }

        public void SaveModel(string strFileName)
        {
            //call function save all frame
            BaseModel.ExportUnitedModel(BaseModel.FileType.PLY, BaseModel.VertexTypes.XYZ_RGB, ArrFrame.ToArray(), strFileName);
        }

        public void SaveFrame(string strFileName,int iSelectedIndex)
        {
            lock (lockThis)
            {
                //call function save all frame
                ArrFrame[iSelectedIndex].Export(BaseModel.FileType.PLY, BaseModel.VertexTypes.XYZ_RGB, _3DPresentation.Utils.Global.GetRealFile(strFileName));
            }
        }


        public void SaveAllFrames(string strPath)
        {
            lock (lockThis)
            {
                //call function save all frame
                BaseModel.ExportAll(BaseModel.VertexTypes.XYZ_RGB, _arrFrame.ToArray(), strPath, BaseModel.FileType.PLY);
            }
        }

        public void ClearAllFrames()
        {
            lock (lockThis)
            {
                //call function save all frame
                for (int i = ArrFrame.Count - 1; i >= 0; i--)
                {
                    DeleteFrame(i);
                }
            }
        }

        //warning: rotation radian
        public void UpdateMatrixAfterFrame(int iIndex, Microsoft.Xna.Framework.Matrix RotationMatrix, Vector3 Translation)
        {
            lock (lockThis)
            { 
                for (int i = iIndex; i < ArrFrame.Count; i++)
                {
                    ArrFrame[i].RotationMatrix *= RotationMatrix;
                    ArrFrame[i].Position += Translation;
                }
            }
        }

        public void UpdateOneFrame(int iIndex, Microsoft.Xna.Framework.Matrix RotationMatrix, Vector3 Translation)
        {
            lock (lockThis)
            {
                ArrFrame[iIndex].RotationMatrix *= RotationMatrix;
                ArrFrame[iIndex].Position += Translation;
            }
        }

        

        public void UpdateMatrixBeforeFrame(int iIndex, Microsoft.Xna.Framework.Matrix RotationMatrix, Vector3 Translation)
        {
            lock (lockThis)
            {
                for (int i = iIndex; i >= 0; i--)
                {
                    ArrFrame[i].RotationMatrix *= RotationMatrix;
                    ArrFrame[i].Position += Translation;
                }
            }
        }

        #endregion

        #region Play Stop Pause Resume Kinect
        COMAutomation ca = null;


        void odControl_Stop(object sender, EventArgs e)
        {
            string[] lines = { "exit" };

            _3DPresentation.Utils.COMAutomation.StopCommand(WorkingDirectory + "\\result\\cm.txt",
                WorkingDirectoryTemp + "\\cm.txt", lines);
        }

        void odControl_Resume(object sender, EventArgs e)
        {
            string[] lines = { "resume" };

            _3DPresentation.Utils.COMAutomation.StopCommand(WorkingDirectory + "\\result\\cm.txt",
                WorkingDirectoryTemp + "\\cm.txt", lines);
        }

        void odControl_Pause(object sender, EventArgs e)
        {

            string[] lines = { "pause" };

            _3DPresentation.Utils.COMAutomation.StopCommand(WorkingDirectory + "\\result\\cm.txt",
                WorkingDirectoryTemp + "\\cm.txt", lines);
        }
        //string strTest = "";
        void ca_CreateFileEvent(object sender, _3DPresentation.Utils.COMAutomation.CreateFileEventArgs e)
        {
            Dispatcher.BeginInvoke(() =>
            {
                lock (lockthis)
                {
                    string strFileName = e.FileName;

                    FileInfo fi = new FileInfo(strFileName);
                    if (fi.Extension.Equals(".ply"))
                    {
                        if (fi.Name.StartsWith("NotDecreaseSameVertex"))
                        {
                            if (OldFileName == strFileName) return;
                            OldFileName = strFileName;
                            //strTest += strFileName + "\n";
                            AddFrame(strFileName);
                        }

                    }
                }
            });
        }

        void odControl_Record(object sender, EventArgs e)
        {
            SetupWorkingDirectory();
            string strQuery =
                string.Format("{0} {1} {2} {3} {4} {5} {6}",
                                WorkingDirectory + "\\recontructor\\rgbd-reconstructor.exe",
                                "player",
                                WorkingDirectory + "\\result",
                                WorkingDirectory + "\\recorded\\grab7",
                                WorkingDirectory + "\\recontructor\\kineck_calibration.yml",
                                WorkingDirectory + "\\recontructor\\NestkConfig.xml",
                                "1");

            //string strQuery =
            //    string.Format("{0} {1} {2} {3} {4} {5} {6}",
            //                    WorkingDirectory + "\\recontructor\\rgbd-reconstructor.exe",
            //                    "kinect",
            //                    WorkingDirectory + "\\result",
            //                    WorkingDirectory + "\\recorded\\grab8",
            //                    WorkingDirectory + "\\recontructor\\kineck_calibration.yml",
            //                    WorkingDirectory + "\\recontructor\\NestkConfig.xml",
            //                    "1");
            COMAutomation.Cmd(strQuery);

            if (ca == null)
            {
                ca = new COMAutomation();
                ca.CreateFileEvent += new COMAutomation.CreateFileEventHandler(ca_CreateFileEvent);

                string strWatchFolder = (WorkingDirectory + "\\result").Replace(@"\", @"\\\\").Replace(@"\\\\\\\\", @"\\\\");
                ca.FolderListener(strWatchFolder);
            }
            else
            {
                ca.CreateFileEvent -= ca_CreateFileEvent2;
                ca.CreateFileEvent -= ca_CreateFileEvent;
                ca.CreateFileEvent += new COMAutomation.CreateFileEventHandler(ca_CreateFileEvent);
            }
        }
        object lockthis = new object();
        string OldFileName = string.Empty;
        void ca_CreateFileEvent2(object sender, _3DPresentation.Utils.COMAutomation.CreateFileEventArgs e)
        {
           Dispatcher.BeginInvoke(() =>
           {
               lock (lockthis)
               {
                   string strFileName = e.FileName;

                   FileInfo fi = new FileInfo(strFileName);
                   if (fi.Extension.Equals(".ply"))
                   {
                       if (fi.Name.StartsWith("NotDecreaseSameVertex"))
                       {
                           if (OldFileName == strFileName) return;
                           OldFileName = strFileName;
                            //strTest += strFileName + "\n";
                            AddFrame(strFileName);
                            odControl.PauseFunction();
                      }

                   }
               }
           });
        }
        void odControl_Capture(object sender, EventArgs e)
        {
            SetupWorkingDirectory();

            string strQuery =
                string.Format("{0} {1} {2} {3} {4} {5} {6}",
                                WorkingDirectory + "\\recontructor\\rgbd-reconstructor.exe",
                                "player",
                                WorkingDirectory + "\\result",
                                WorkingDirectory + "\\recorded\\grab7",
                                WorkingDirectory + "\\recontructor\\kineck_calibration.yml",
                                WorkingDirectory + "\\recontructor\\NestkConfig.xml",
                                "0");
            //string strQuery =
            //    string.Format("{0} {1} {2} {3} {4} {5} {6}",
            //                    WorkingDirectory + "\\recontructor\\rgbd-reconstructor.exe",
            //                    "kinect",
            //                    WorkingDirectory + "\\result",
            //                    WorkingDirectory + "\\recorded\\grab8",
            //                    WorkingDirectory + "\\recontructor\\kineck_calibration.yml",
            //                    WorkingDirectory + "\\recontructor\\NestkConfig.xml",
            //                    "0");
            COMAutomation.Cmd(strQuery);

            if (ca == null)
            {
                ca = new COMAutomation();
                ca.CreateFileEvent += new COMAutomation.CreateFileEventHandler(ca_CreateFileEvent2);

                string strWatchFolder = (WorkingDirectory + "\\result").Replace(@"\", @"\\\\").Replace(@"\\\\\\\\", @"\\\\");
                ca.FolderListener(strWatchFolder);
            }
            else
            {
                ca.CreateFileEvent -= ca_CreateFileEvent2;
                ca.CreateFileEvent -= ca_CreateFileEvent;
                ca.CreateFileEvent += new COMAutomation.CreateFileEventHandler(ca_CreateFileEvent2);
            }
        }

        #endregion

        private void ContentHomePage_SizeChanged(object sender, SizeChangedEventArgs e)
        {
            frameViewer.SetActualWidthAndHeight(ContentHomePage.ActualWidth, ContentHomePage.ActualHeight);
            vcOjectViewer.Width = ContentHomePage.ActualWidth;
            vcOjectViewer.Height = ContentHomePage.ActualHeight;
        }

        //private void Button_Click(object sender, RoutedEventArgs e)
        //{
        //    System.Windows.Media.Imaging.WriteableBitmap wbm = new System.Windows.Media.Imaging.WriteableBitmap(300, 300).FromResource("Views/Editor/Images/rotation_bg.png");
        //    //System.Windows.Media.Imaging.WriteableBitmapExtensions.Clear(wbm, System.Windows.Media.Color.FromArgb(255, 255, 0, 0));
        //    this.currentImage.Source = wbm;
        //    OpenFileDialog dlg = new OpenFileDialog(); // new instance
        //    dlg.Multiselect = true;
        //    dlg.Filter = "ply|*.ply";
        //    if ((bool)dlg.ShowDialog())
        //    {
        //        foreach (FileInfo fi in dlg.Files)
        //        {
        //            string strPath = fi.FullName;
        //            strPath = strPath.Replace(".ply", ".jpg");
        //            //ParentEditor.AddFrame(fi, strPath);

        //            AddFrame(fi);
                    
        //        }
        //    }

        //    //_3DPresentation.Views.customChildWindow cw = new Views.customChildWindow();

        //    //_3DPresentation.Views.ObjectView ov = new Views.ObjectView();
        //    //cw.AddContent(ov);
        //    //cw.Show(this);
        //}
    }
}