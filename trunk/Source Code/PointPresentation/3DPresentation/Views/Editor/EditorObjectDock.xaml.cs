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

        private void btNewCaptureModel_Click(object sender, RoutedEventArgs e)
        {

        }

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
                    ParentEditor.AddFrame(arrFrameName[i], arrFrameThumnail[i]);
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
            MessageBox.Show("asdasd");
        }
    }
}
