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

namespace _3DPresentation.Views.Editor
{
    public partial class SimplePopupContent : UserControl
    {
        public SimplePopupContent()
        {
            InitializeComponent();
        }

        EditorView _parent;

        public EditorView ParentView
        {
            get { return _parent; }
            set { _parent = value; }
        }

        public int imgIndex = -1;

        private void btDeleteImage_Click(object sender, RoutedEventArgs e)
        {
            //ParentView
            ParentView.DeleteFrame(imgIndex);
        }

        private void btSetFixedFrame_Click(object sender, RoutedEventArgs e)
        {
            ParentView.FixedImageIndex = imgIndex;
        }

        private void btSetReferenceFrame_Click(object sender, RoutedEventArgs e)
        {
            try
            {
                ParentView.ReferenceImageIndex = imgIndex;
                MessageBox.Show(imgIndex.ToString());
            }
            catch (Exception ex)
            {
                MessageBox.Show(ex.Message);
            }
        }
    }
}
