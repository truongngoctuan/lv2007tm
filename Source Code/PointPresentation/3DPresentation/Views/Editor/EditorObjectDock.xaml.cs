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
using System.Threading;
using _3DPresentation.Models;
using _3DPresentation.Utils;
using System.IO;

namespace _3DPresentation.Views.Editor
{
    public partial class EditorObjectDock : UserControl
    {

        EditorView _parent;

        public EditorView ParentEditor
        {
            get { return _parent; }
            set { _parent = value; }
        }

        public EditorObjectDock()
        {
            InitializeComponent();
        }

        #region NewCaptureModel
        COMAutomation ca = new COMAutomation();
        private void btNewCaptureModel_Click(object sender, RoutedEventArgs e)
        {
            ParentEditor.SetupWorkingDirectory();
            string strQuery =
                string.Format("{0} {1} {2} {3} {4}",
                              ParentEditor.WorkingDirectory + "\\recontructor\\rgbd-reconstructor.exe",
                              "player",
                              ParentEditor.WorkingDirectory + "\\result",
                              ParentEditor.WorkingDirectory + "\\recorded\\grab7",
                              ParentEditor.WorkingDirectory + "\\recontructor\\kineck_calibration.yml");
            COMAutomation.Cmd(strQuery);

            ca.CreateFileEvent += new EventHandler(ca_CreateFileEvent);
            ca.DeleteFileEvent += new EventHandler(ca_DeleteFileEvent);

            string strWatchFolder = (ParentEditor.WorkingDirectory + "\\result").Replace(@"\", @"\\\\").Replace(@"\\\\\\\\", @"\\\\");
            ca.FolderListener(strWatchFolder);
        }

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
                        ParentEditor.AddFrame(strFileName, new PathUri(_3DPresentation.Utils.Global.GetRandomSnapshot(), false));
                    }

                }
            });
        }
        #endregion

        private void btPlay_Click(object sender, RoutedEventArgs e)
        {
            this.Dispatcher.BeginInvoke(new Action(() => {

                try
                {
                List<string> arrFrameName = new List<string>();
                arrFrameName.Add("d:\\NotDecreaseSameVertex_0000.ply");
                arrFrameName.Add("d:\\NotDecreaseSameVertex_0005.ply");
                arrFrameName.Add("d:\\NotDecreaseSameVertex_0015.ply");
                arrFrameName.Add("d:\\NotDecreaseSameVertex_0025.ply");
                arrFrameName.Add("d:\\NotDecreaseSameVertex_0035.ply");
                arrFrameName.Add("d:\\NotDecreaseSameVertex_0045.ply");
                arrFrameName.Add("d:\\NotDecreaseSameVertex_0055.ply");
                arrFrameName.Add("d:\\NotDecreaseSameVertex_0065.ply");

                List<string> arrFrameThumnail = new List<string>();
                arrFrameThumnail.Add("d:\\NotDecreaseSameVertex_0000.jpg");
                arrFrameThumnail.Add("d:\\NotDecreaseSameVertex_0005.jpg");
                arrFrameThumnail.Add("d:\\NotDecreaseSameVertex_0015.jpg");
                arrFrameThumnail.Add("d:\\NotDecreaseSameVertex_0025.jpg");
                arrFrameThumnail.Add("d:\\NotDecreaseSameVertex_0035.jpg");
                arrFrameThumnail.Add("d:\\NotDecreaseSameVertex_0045.jpg");
                arrFrameThumnail.Add("d:\\NotDecreaseSameVertex_0055.jpg");
                arrFrameThumnail.Add("d:\\NotDecreaseSameVertex_0065.jpg");

                for (int i = 0; i < arrFrameName.Count; i++)
                {
                    ParentEditor.AddFrame(arrFrameName[i], new PathUri(arrFrameThumnail[i], true));
                    //System.Threading.Thread.Sleep(2000);
                }
                }
                catch (Exception ex)
                {
                    MessageBox.Show(ex.Message);
                }
            }));
        }

        private void btStop_Click(object sender, RoutedEventArgs e)
        {
            string[] lines = { "exit" };

            _3DPresentation.Utils.COMAutomation.StopCommand(ParentEditor.WorkingDirectory + "\\result\\cm.txt",
                ParentEditor.WorkingDirectoryTemp + "\\cm.txt", lines);
        }


    }
}
