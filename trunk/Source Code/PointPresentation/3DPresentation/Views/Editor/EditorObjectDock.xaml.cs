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
using System.Windows.Media.Imaging;

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

            SetEnable(true, false, false);
        }

        void SetEnable(bool bPlay, bool bPause, bool bStop)
        {
            btPlay.IsEnabled = bPlay;
            btPause.IsEnabled = bPause;
            btStop.IsEnabled = bStop;

            if (btPlay.IsEnabled)
            {
                imgPlay.Source = new BitmapImage(_3DPresentation.Utils.Global.MakePackUri("Views/Editor/Images/top_play.png"));
            }
            else
            {
                imgPlay.Source = new BitmapImage(_3DPresentation.Utils.Global.MakePackUri("Views/Editor/Images/top_play_gray.png"));
            }

            if (btPause.IsEnabled)
            {
                imgPause.Source = new BitmapImage(_3DPresentation.Utils.Global.MakePackUri("Views/Editor/Images/top_pause.png"));
            }
            else
            {
                imgPause.Source = new BitmapImage(_3DPresentation.Utils.Global.MakePackUri("Views/Editor/Images/top_pause_gray.png"));
            }

            if (btStop.IsEnabled)
            {
                imgStop.Source = new BitmapImage(_3DPresentation.Utils.Global.MakePackUri("Views/Editor/Images/top_stop.png"));
            }
            else
            {
                imgStop.Source = new BitmapImage(_3DPresentation.Utils.Global.MakePackUri("Views/Editor/Images/top_stop_gray.png"));
            }
        }

        #region NewCaptureModel
        
        private void btNewCaptureModel_Click(object sender, RoutedEventArgs e)
        {
            this.Dispatcher.BeginInvoke(new Action(() =>
            {

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

        #endregion

        private void btPlay_Click(object sender, RoutedEventArgs e)
        {
            if (btStop.IsEnabled)
            {
                //resume 
                SetEnable(false, true, true);

                if (Resume != null)
                {
                    Resume(this, new EventArgs());
                }
            }
            else
            {//play
                SetEnable(false, true, true);

                if (Play != null)
                {
                    Play(this, new EventArgs());
                }

            }
        }

        private void btStop_Click(object sender, RoutedEventArgs e)
        {
            if (Stop != null)
            {
                Stop(this, new EventArgs());
            }

            SetEnable(true, false, false);
        }

        private void btPause_Click(object sender, RoutedEventArgs e)
        {
            //gui lenh pause
            SetEnable(true, false, true);

            if (Pause != null)
            {
                Pause(this, new EventArgs());
            }
        }

        public event EventHandler Play;
        public event EventHandler Pause;
        public event EventHandler Resume;
        public event EventHandler Stop;

    }
}
