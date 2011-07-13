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

                ck.DownloadCompleted += new EventHandler((a, b) =>
                {
                    SilverlightMessageBoxLibrary.Message.InfoMessage("Download Done!");
                    //_3DPresentation.Views.customChildWindow cw = new Views.customChildWindow();

                    //TextBlock tblock = new TextBlock();
                    //tblock.Text = "Download Done!";
                    //tblock.Width = 100;
                    //tblock.Height = 50;
                    //tblock.VerticalAlignment = System.Windows.VerticalAlignment.Center;
                    //tblock.HorizontalAlignment = System.Windows.HorizontalAlignment.Center;
                    //cw.AddContent(tblock);
                    //cw.Show(this.ParentEditor);
                });
            }
            catch (Exception ex)
            {
                MessageBox.Show(ex.Message);
                throw;
            }
        }
        #region setup workspace
        private void btSetupWorkSpace_Click(object sender, RoutedEventArgs e)
        {
            FolderDialogSL4.FolderDialog FolderDlg = new FolderDialogSL4.FolderDialog();
            //FolderDlg.Show();
            FolderDlg.Closed += new EventHandler(cw_Closed);
            FolderDlg.Show();
        }

        void cw_Closed(object sender, EventArgs e)
        {
            FolderDialogSL4.FolderDialog fd = sender as FolderDialogSL4.FolderDialog;

            if (fd.DialogResult == true)
            {
                ParentEditor.WorkingDirectory = fd.txtSelectedFolder.Text;
                ParentEditor.SetupWorkingDirectory();

                if (!ClientFileAndDirectory.FolderExists(ParentEditor.WorkingDirectory)) ClientFileAndDirectory.CreateFolder(ParentEditor.WorkingDirectory);
                if (!ClientFileAndDirectory.FolderExists(ParentEditor.WorkingDirectoryTemp)) ClientFileAndDirectory.CreateFolder(ParentEditor.WorkingDirectoryTemp);
                if (!ClientFileAndDirectory.FolderExists(ParentEditor.WorkingDirectory + "\\result")) ClientFileAndDirectory.CreateFolder(ParentEditor.WorkingDirectoryTemp + "\\result");
                if (!ClientFileAndDirectory.FolderExists(ParentEditor.WorkingDirectory + "\\recorded")) ClientFileAndDirectory.CreateFolder(ParentEditor.WorkingDirectoryTemp + "\\recorded");
            }
        }
        #endregion

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
                    ParentEditor.AddFrame(fi);
                }
            }
        }

        private void btSaveModel_Click(object sender, RoutedEventArgs e)
        {
            SaveFileDialog dlg = new SaveFileDialog(); // new instance
            dlg.Filter = "ply|*.ply";
            if ((bool)dlg.ShowDialog())
            {
                string strPath = dlg.SafeFileName;
                ParentEditor.SaveModel(strPath);
                SilverlightMessageBoxLibrary.Message.InfoMessage("Save Done!");
            }
        }

        private void btMatch2FrameManual_Click(object sender, RoutedEventArgs e)
        {
            //setup 2 parameter
            //catch result
            //recal
            if (ParentEditor.FixedImageIndex == -1 || ParentEditor.ReferenceImageIndex == -1)
            {
                MessageBox.Show("error!!");
                return;
            }

            MatchModelManual pgContent = new MatchModelManual();
            pgContent.MatchManualFinished += new MatchModelManual.TranslationRotationEventHandler(pg_MatchManualFinished);
            pgContent.SetInputData(ParentEditor.FixedImageIndex, ParentEditor.ReferenceImageIndex);
            pgContent.SetInputData(ParentEditor.ArrFrame[ParentEditor.FixedImageIndex], ParentEditor.ArrFrame[ParentEditor.ReferenceImageIndex]);

            _3DPresentation.Views.customChildWindow cw = new Views.customChildWindow();
            pgContent.CancelButtonClick +=new EventHandler((a, b)=>{
                cw.Close();
            });
            pgContent.OKButtonClick += new EventHandler((a, b) =>
            {
                cw.Close();
            });
            
            cw.AddContent(pgContent);
            cw.Show(this.ParentEditor);
        }

        void pg_MatchManualFinished(object sender, MatchModelManual.TranslationRotationEventArgs e)
        {
            ParentEditor.UpdateMatrixAfterFrame(e.ReferenceIndex, e.RotationMatrix, e.TransitionMatrix);
        }

        private void btSaveAllFrames_Click(object sender, RoutedEventArgs e)
        {
            SaveFileDialog dlg = new SaveFileDialog(); // new instance
            dlg.Filter = "ply|*.ply";
            if ((bool)dlg.ShowDialog())
            {
                string strPath = dlg.SafeFileName;
                strPath = strPath.Replace(".ply", "");
                ParentEditor.SaveAllFrames(strPath);
                SilverlightMessageBoxLibrary.Message.InfoMessage("Save Done!");
            }
        }

        private void btClearCurrentFrames_Click(object sender, RoutedEventArgs e)
        {
            ParentEditor.ClearAllFrames();
            SilverlightMessageBoxLibrary.Message.InfoMessage("Clear Done!");
        }
    }
}
