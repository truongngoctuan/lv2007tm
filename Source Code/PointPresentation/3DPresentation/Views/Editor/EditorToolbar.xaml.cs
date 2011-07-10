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
using System.IO;

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

            //cwSetupSDK cwNew = new cwSetupSDK();
            //cwNew.Show();
        }

        #region setup workspace
        private void btSetupWorkSpace_Click(object sender, RoutedEventArgs e)
        {
            FolderDialogSL4.FolderDialog FolderDlg = new FolderDialogSL4.FolderDialog();
            FolderDlg.Show();
            FolderDlg.Closed += new EventHandler(cw_Closed);
            FolderDlg.Show();
        }

        void cw_Closed(object sender, EventArgs e)
        {
            FolderDialogSL4.FolderDialog fd = sender as FolderDialogSL4.FolderDialog;

            if (fd.DialogResult == true)
            {
                ParentEditor.WorkingDirectory = fd.txtSelectedFolder.Text;
            }
        }
        #endregion

        private void btResetWorkSpace_Click(object sender, RoutedEventArgs e)
        {
            cwResetWorkSpace cwNew = new cwResetWorkSpace();
            cwNew.Show();
        }

        private void btOpenModel_Click(object sender, RoutedEventArgs e)
        {
            OpenFileDialog dlg = new OpenFileDialog(); // new instance
            dlg.Multiselect = true;
            dlg.Filter = "ply|*.ply";
            if ((bool)dlg.ShowDialog())
            {
                foreach (FileInfo fi in dlg.Files)
                {
                    string strPath = fi.FullName;
                    strPath = strPath.Replace(".ply", ".jpg");
                    ParentEditor.AddFrame(fi, strPath);
                }
            }

            //cwOpenModel cwNew = new cwOpenModel();
            //cwNew.Show();
        }

        private void btSaveModel_Click(object sender, RoutedEventArgs e)
        {
            SaveFileDialog dlg = new SaveFileDialog(); // new instance
            dlg.Filter = "ply|*.ply";
            if ((bool)dlg.ShowDialog())
            {
                string strPath = dlg.SafeFileName;
                ParentEditor.SaveModel(strPath);
                MessageBox.Show(strPath);
            }

            //cwSaveModel cwNew = new cwSaveModel();
            //cwNew.Show();
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
            //BaseModel newModel1 = PointModel.Import(new System.IO.FileInfo("d:\\NotDecreaseSameVertex_0000.ply"));
            //BaseModel newModel2 = PointModel.Import(new System.IO.FileInfo("d:\\NotDecreaseSameVertex_0035.ply"));
            pg.SetInputData(ParentEditor.ArrFrame[ParentEditor.FixedImageIndex], ParentEditor.ArrFrame[ParentEditor.ReferenceImageIndex]);

            App.GoToPage(pg);
        }
    }
}
