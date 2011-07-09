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
    public partial class EditorToolbar : UserControl
    {
        EditorView _parent;

        public EditorView ParentEditor
        {
            get { return _parent; }
            set { _parent = value; }
        }
        public EditorToolbar()
        {
            InitializeComponent();
        }
        
        private void btSetupSDK_Click(object sender, RoutedEventArgs e)
        {
            try
            {
                ParentEditor.SetupWorkingDirectory();
                ClientPackage ck = new ClientPackage();
                ck.DownloadtoClient("/recontructor.zip", ParentEditor.WorkingDirectory);
            }
            catch (Exception ex)
            {
                MessageBox.Show(ex.Message);
                throw;
            }

            cwSetupSDK cwNew = new cwSetupSDK();
            cwNew.Show();
        }

        private void btSetupWorkSpace_Click(object sender, RoutedEventArgs e)
        {
            //OpenFileDialog dlg = new OpenFileDialog();
            //dlg.ShowDialog();
            cwSetupWorkSpace cwNew = new cwSetupWorkSpace();
            cwNew.Show();
        }

        private void btResetWorkSpace_Click(object sender, RoutedEventArgs e)
        {
            cwResetWorkSpace cwNew = new cwResetWorkSpace();
            cwNew.Show();
        }

        private void btOpenModel_Click(object sender, RoutedEventArgs e)
        {
            cwOpenModel cwNew = new cwOpenModel();
            cwNew.Show();
        }

        private void btSaveModel_Click(object sender, RoutedEventArgs e)
        {
            cwSaveModel cwNew = new cwSaveModel();
            cwNew.Show();
        }

        private void btOptimize_Click(object sender, RoutedEventArgs e)
        {
            cwOptimize cwNew = new cwOptimize();
            cwNew.Show();
        }

        private void btMatch2FrameManual_Click(object sender, RoutedEventArgs e)
        {
            //setup 2 parameter
            //catch result
            //recal
            MatchModelView pg = new MatchModelView();
            pg.ParentView = _parent;
            pg.SetInputData(ParentEditor.FixedImageIndex, ParentEditor.ReferenceImageIndex);
            BaseModel newModel1 = PointModel.Import(new System.IO.FileInfo("d:\\NotDecreaseSameVertex_0000.ply"));
            BaseModel newModel2 = PointModel.Import(new System.IO.FileInfo("d:\\NotDecreaseSameVertex_0020.ply"));

            pg.SetInputData(newModel1, newModel2);

            App.GoToPage(pg);
        }
    }
}
