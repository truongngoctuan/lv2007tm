using System.Windows;
using System.Windows.Controls;
using System.Windows.Input;
using System.Runtime.InteropServices.Automation;
using System.Runtime.InteropServices;
using System.Collections.ObjectModel;

namespace FolderDialogSL4
{
    public partial class FolderDialog : ChildWindow
    {
        #region Fields
        public string SelectedFolderPath = string.Empty;
        private string CurrentPath = string.Empty;
        private ObservableCollection<Folder> FolderList; 
        #endregion

        #region Constructor
        public FolderDialog()
        {
            InitializeComponent();

            #region Get Drives
            dynamic fileSystem = AutomationFactory.CreateObject("Scripting.FileSystemObject");
            dynamic drives = fileSystem.Drives;

            foreach (var drive in drives)
            {
                try
                {
                    Drive dr = new Drive();
                    if (string.IsNullOrEmpty(drive.VolumeName))
                    {
                        dr.VolumeName = "Local Disk";
                    }
                    else
                    {
                        dr.VolumeName = drive.VolumeName;
                    }
                    dr.DriveLetter = drive.DriveLetter;

                    TreeViewItem tvi = new TreeViewItem();
                    tvi.HeaderTemplate = this.Resources["DriveHeaderTemplate"] as DataTemplate;
                    tvi.Header = string.Format("{0} ({1}:)", dr.VolumeName, dr.DriveLetter);
                    tvi.Tag = dr.DriveLetter;
                    tvi.Selected += new RoutedEventHandler(Drive_Selected);

                    MyComputerItem.Items.Add(tvi);
                }
                catch (COMException) { }
            }
            #endregion
        } 
        #endregion

        #region Drive Selected
        void Drive_Selected(object sender, RoutedEventArgs e)
        {
            TreeViewItem tvi = sender as TreeViewItem;

            if (tvi.Header.ToString() != "My Computer")
            {
                GetFolders(tvi.Tag.ToString());

                if (FoldersLB.ItemsSource != null)
                {
                    FoldersLB.ItemsSource = null;
                }

                if (FolderList != null && FolderList.Count > 0)
                {
                    FoldersLB.ItemsSource = FolderList;
                }

                BackButton.IsEnabled = false;
                CurrentPath = tvi.Tag.ToString();
            }
        } 
        #endregion

        #region Get Folders from the Drive Selected
        private void GetFolders(string path)
        {
            dynamic fileSystem = AutomationFactory.CreateObject("Scripting.FileSystemObject");
            dynamic folders = fileSystem.GetFolder(string.Format(@"{0}:\", path)).SubFolders;

            GetFolders(folders);
        } 
        #endregion

        #region Get SubFolders from Current Folder Selection
        private void GetSubFolders(string currentSelection)
        {
            dynamic fileSystem = AutomationFactory.CreateObject("Scripting.FileSystemObject");
            dynamic folders = fileSystem.GetFolder(string.Format(@"{0}", currentSelection)).SubFolders;

            GetFolders(folders);

            if (CurrentPath.Split('\\').Length > 0)
            {
                BackButton.IsEnabled = true;
            }
            else
            {
                BackButton.IsEnabled = false;
            }
        } 
        #endregion

        #region Get Folders dynamically
        private void GetFolders(dynamic folders)
        {
            FolderList = new ObservableCollection<Folder>();

            foreach (var folder in folders)
            {
                try
                {
                    Folder fld = new Folder();
                    fld.FolderName = folder.Name;
                    fld.FolderPath = folder.Path;

                    FolderList.Add(fld);
                }
                catch (System.Exception) { }
            }
        } 
        #endregion

        #region Dialog Result Clicks
        private void OKButton_Click(object sender, RoutedEventArgs e)
        {
            this.DialogResult = true;
        }

        private void CancelButton_Click(object sender, RoutedEventArgs e)
        {
            this.DialogResult = false;
        } 
        #endregion

        #region Folder SelectionChanged
        private void Folder_SelectionChanged(object sender, SelectionChangedEventArgs e)
        {
            if (FoldersLB.SelectedItem != null)
            {
                txtSelectedFolder.Text = (FoldersLB.SelectedItem as Folder).FolderPath;
                SelectedFolderPath = (FoldersLB.SelectedItem as Folder).FolderPath;
            }
        } 
        #endregion

        #region Double Click Handler
        private void DummyRectForDoubleClick_Loaded(object sender, RoutedEventArgs e)
        {
            DoubleClickHelper.DoubleClickHandler dblClickHandler = new DoubleClickHelper.DoubleClickHandler(Folder_DoubleClick);
            DoubleClickHelper dch = new DoubleClickHelper();
            dch.AttachDoubleClick(sender, dblClickHandler);
        } 
        #endregion

        #region Selected Folder DoubleClick
        private void Folder_DoubleClick(object sender, MouseButtonEventArgs e)
        {
            Folder subItem = (Folder)FoldersLB.SelectedItem;

            GetSubFolders(subItem.FolderPath);

            if (FoldersLB.ItemsSource != null)
            {
                FoldersLB.ItemsSource = null;
            }

            if (FolderList != null && FolderList.Count > 0)
            {
                FoldersLB.ItemsSource = FolderList;
            }

            CurrentPath = subItem.FolderPath;
        } 
        #endregion

        #region Back Button Click
        private void Back_Click(object sender, RoutedEventArgs e)
        {
            if (!string.IsNullOrEmpty(CurrentPath))
            {
                string[] paths = CurrentPath.Split('\\');
                string path = string.Empty;

                for (int i = 0; i < paths.Length - 1; i++)
                {
                    path += paths[i] + "\\";
                }

                path = path.Remove(path.Length - 1, 1);

                if (path.Length == 2)
                {
                    path = path.Substring(0, 1);
                    GetFolders(path);

                    BackButton.IsEnabled = false;
                }
                else
                {
                    GetSubFolders(path);
                }

                if (FoldersLB.ItemsSource != null)
                {
                    FoldersLB.ItemsSource = null;
                }

                if (FolderList != null && FolderList.Count > 0)
                {
                    FoldersLB.ItemsSource = FolderList;
                    CurrentPath = path;

                    if (path.Length == 1)
                    {
                        txtSelectedFolder.Text = path + ":\\";
                    }
                    else
                    {
                        txtSelectedFolder.Text = path;
                    }
                    
                }
            }
        } 
        #endregion
    }
}

