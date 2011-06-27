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
using System.IO;
using System.Windows.Media.Imaging;

namespace _3DPresentation
{
    public partial class OpenFileControl : UserControl
    {
        public OpenFileControl()
        {
            InitializeComponent();
            btOpen.Click += new RoutedEventHandler(btOpen_Click);
        }

        public string Label
        {
            get
            {
                return btOpen.Content.ToString();
            }
            set
            {
                btOpen.Content = value;
            }
        }

        void btOpen_Click(object sender, RoutedEventArgs e)
        {
            OpenFileDialog dialog = new OpenFileDialog();
            dialog.Multiselect = false;
            dialog.Filter = "Model|*.ply|Text|*.txt|All Files|*.*";
            if(dialog.ShowDialog() == true)
            {
                Dispatcher.BeginInvoke(new Action(() => { lbContent.Content = dialog.File.Name; }));
                //using (StreamReader reader = dialog.File.OpenText()) 
                //{
                //    // Store file content in 'text' variable
                //    string text = reader.ReadToEnd();
                //}
                //using (Stream stream = dialog.File.OpenRead())
                //{
                //    // Store file content in 'text' variable
                //    BitmapImage bitmapImage = new BitmapImage();
                //    bitmapImage.SetSource(stream);
                //    img.Source = bitmapImage;
                //}
                if (this.FileOpened != null)
                    FileOpened(this, new FileOpenedEventArgs(dialog.File));
            }
        }

        public delegate void FileOpenedHandler(object sender, FileOpenedEventArgs e);
        public event FileOpenedHandler FileOpened;

        public class FileOpenedEventArgs : EventArgs
        {
            public FileInfo FileInfo
            {
                get;
                set;
            }

            public FileOpenedEventArgs(FileInfo fileInfo)
                : base()
            {
                FileInfo = fileInfo;
            }
        }
    }
}
