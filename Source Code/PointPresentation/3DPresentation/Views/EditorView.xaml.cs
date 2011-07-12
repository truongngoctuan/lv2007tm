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

        }
        #endregion

        private Popup simplePopup = new Popup();

        public EditorView()
        {
            InitializeComponent();
            this.KeyDown += new KeyEventHandler(EditorView_KeyDown);

            toolbar.ParentEditor = this;
            frameViewer.ParentView = this;
            odControl.ParentEditor = this;

            ArrFrame = new List<BaseModel>();

            //BaseModel newModel = PointModel.Import(new System.IO.FileInfo("d:\\NotDecreaseSameVertex_0000.ply"));
            //vcOjectViewer.AddModel(newModel);
            //vcOjectViewer.SetTarget(newModel);

            odControl.Play += new EventHandler(odControl_Play);
            odControl.Pause += new EventHandler(odControl_Pause);
            odControl.Resume += new EventHandler(odControl_Resume);
            odControl.Stop += new EventHandler(odControl_Stop);

        }

        void EditorView_KeyDown(object sender, KeyEventArgs e)
        {

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

                    Babylon.Toolbox.OrbitCamera cam = new Babylon.Toolbox.OrbitCamera { Alpha = (float)Math.PI / 2 };

                    //setmodel target
                    cam.Radius = model.BoundingInfo.BoundingSphereWorld.Radius * 4.0f;
                    cam.Target = model.BoundingInfo.BoundingSphereWorld.Center;
                    cam.Alpha = cam.Alpha; // to raise event => recompute Position to get new ViewMatrix

                    frameViewer.AddImage(model.toBitmap(400, 400, cam));

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
        }

        public void SaveFrame(string strFileName)
        {
            lock (lockThis)
            {
                //call function save all frame
                ArrFrame[frameViewer.SelectedIndex].Export(BaseModel.FileType.PLY, BaseModel.VertexType.XYZ_RGB, _3DPresentation.Utils.Global.GetRealFile(strFileName));
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

        public void UpdateMatrixBeforeFrame(int iIndex, Microsoft.Xna.Framework.Matrix RotationMatrix, Vector3 Translation)
        {
            lock (lockThis)
            {
                for (int i = iIndex; i <= iIndex; i++)
                {
                    ArrFrame[i].RotationMatrix *= RotationMatrix;
                    ArrFrame[i].Position += Translation;
                }
            }
        }

        #endregion

        #region Play Stop Pause Resume Kinect
        COMAutomation ca = new COMAutomation();

        void ca_DeleteFileEvent(object sender, EventArgs e)
        {
            //throw new NotImplementedException();
        }

        void ca_CreateFileEvent(object sender, EventArgs e)
        {
            Dispatcher.BeginInvoke(() =>
            {
                string strFileName = ca.FileName;

                FileInfo fi = new FileInfo(strFileName);
                if (fi.Extension.Equals(".ply"))
                {
                    if (fi.Name.StartsWith("NotDecreaseSameVertex"))
                    {
                        AddFrame(strFileName);
                    }

                }
            });
        }
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


        void odControl_Play(object sender, EventArgs e)
        {
            SetupWorkingDirectory();
            string strQuery =
                string.Format("{0} {1} {2} {3} {4}",
                                WorkingDirectory + "\\recontructor\\rgbd-reconstructor.exe",
                                "player",
                                WorkingDirectory + "\\result",
                                WorkingDirectory + "\\recorded\\grab7",
                                WorkingDirectory + "\\recontructor\\kineck_calibration.yml");
            COMAutomation.Cmd(strQuery);

            ca.CreateFileEvent += new EventHandler(ca_CreateFileEvent);
            ca.DeleteFileEvent += new EventHandler(ca_DeleteFileEvent);

            string strWatchFolder = (WorkingDirectory + "\\result").Replace(@"\", @"\\\\").Replace(@"\\\\\\\\", @"\\\\");
            ca.FolderListener(strWatchFolder);
        }
        #endregion

        private void Button_Click(object sender, RoutedEventArgs e)
        {
            System.Windows.Media.Imaging.WriteableBitmap wbm = new System.Windows.Media.Imaging.WriteableBitmap(300, 300).FromResource("Views/Editor/Images/rotation_bg.png");
            //System.Windows.Media.Imaging.WriteableBitmapExtensions.Clear(wbm, System.Windows.Media.Color.FromArgb(255, 255, 0, 0));
            this.currentImage.Source = wbm;
            OpenFileDialog dlg = new OpenFileDialog(); // new instance
            dlg.Multiselect = true;
            dlg.Filter = "ply|*.ply";
            if ((bool)dlg.ShowDialog())
            {
                foreach (FileInfo fi in dlg.Files)
                {
                    string strPath = fi.FullName;
                    strPath = strPath.Replace(".ply", ".jpg");
                    //ParentEditor.AddFrame(fi, strPath);

                    AddFrame(fi);
                    
                }
            }

            //_3DPresentation.Views.customChildWindow cw = new Views.customChildWindow();

            //_3DPresentation.Views.ObjectView ov = new Views.ObjectView();
            //cw.AddContent(ov);
            //cw.Show(this);
        }
    }
}