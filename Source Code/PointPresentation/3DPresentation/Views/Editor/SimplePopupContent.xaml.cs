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
using System.Windows.Controls.Primitives;

namespace _3DPresentation.Views.Editor
{
    public partial class SimplePopupContent : UserControl
    {
        public int SelectedIndex;
        public SimplePopupContent()
        {
            InitializeComponent();

            //http://forums.silverlight.net/forums/p/2260/462506.aspx
            
            myDispatcherTimer.Interval = new TimeSpan(0, 0, 0, 0, 3000);
            myDispatcherTimer.Tick += new EventHandler(myDispatcherTimer_Tick);
            myDispatcherTimer.Start();

        }
        System.Windows.Threading.DispatcherTimer myDispatcherTimer = new System.Windows.Threading.DispatcherTimer();
        void myDispatcherTimer_Tick(object sender, EventArgs e)
        {
            //throw new NotImplementedException();
            //end popup after timer finished
            StopTimer();
        }

        public void StopTimer()
        {
            ParentView.ClosePopup();
            myDispatcherTimer.Stop();
            myDispatcherTimer.Tick -= myDispatcherTimer_Tick;
        }

        EditorView _parent;

        public EditorView ParentView
        {
            get { return _parent; }
            set { _parent = value; }
        }

        private void btDeleteImage_Click(object sender, RoutedEventArgs e)
        {
            ParentView.DeleteFrame(SelectedIndex);
            StopTimer();
        }

        private void btSetFixedFrame_Click(object sender, RoutedEventArgs e)
        {
            ParentView.SetFixedImageIndex(SelectedIndex);
            StopTimer();
        }

        private void btSetReferenceFrame_Click(object sender, RoutedEventArgs e)
        {
            ParentView.SetReferenceImageIndex(SelectedIndex);
            StopTimer();
        }

        private void btSaveFrame_Click(object sender, RoutedEventArgs e)
        {
            SaveFileDialog dlg = new SaveFileDialog(); // new instance
            dlg.Filter = "ply|*.ply";
            if ((bool)dlg.ShowDialog())
            {
                string strPath = dlg.SafeFileName;
                ParentView.SaveFrame(strPath);

                //MessageBox.Show(strPath);
            }
        }
    }
}
