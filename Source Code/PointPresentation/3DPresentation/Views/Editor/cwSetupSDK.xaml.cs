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
using _3DPresentation.Models;

namespace _3DPresentation.Views.Editor
{
    public partial class cwSetupSDK : ChildWindow
    {
        public cwSetupSDK()
        {
            InitializeComponent();

            BaseModel newModel1 = PointModel.Import(new System.IO.FileInfo("d:\\NotDecreaseSameVertex_0000.ply"));
            vcOjectViewer.AddModel(newModel1);
            //vcOjectViewer.AddModel(_model2);
            vcOjectViewer.SetTarget(newModel1);
        }

        private void OKButton_Click(object sender, RoutedEventArgs e)
        {
            this.DialogResult = true;
        }

        private void CancelButton_Click(object sender, RoutedEventArgs e)
        {
            this.DialogResult = false;
        }
    }
}

