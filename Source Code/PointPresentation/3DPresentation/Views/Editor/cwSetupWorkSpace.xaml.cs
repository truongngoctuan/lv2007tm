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
using FolderDialogSL4;

namespace _3DPresentation.Views.Editor
{
    public partial class cwSetupWorkSpace : ChildWindow
    {
        public cwSetupWorkSpace()
        {
            InitializeComponent();
            txtPath.Text = "d:\\\\test2";
        }

        private void OKButton_Click(object sender, RoutedEventArgs e)
        {
            this.DialogResult = true;
        }

        private void CancelButton_Click(object sender, RoutedEventArgs e)
        {
            this.DialogResult = false;
        }

        #region Select Folder Click
        private void SelectFolder_Click(object sender, RoutedEventArgs e)
        {
            FolderDialog fd = new FolderDialog();
            fd.Closed += new EventHandler(cw_Closed);
            fd.Show();
        }
        #endregion

        #region Folder Dialog Closed
        void cw_Closed(object sender, EventArgs e)
        {
            FolderDialog fd = sender as FolderDialog;

            if (fd.DialogResult == true)
            {
                txtPath.Text = fd.txtSelectedFolder.Text;
            }
        }
        #endregion
    }
}

