using System;
using System.IO;
using System.Reflection;
using System.Windows;
using Microsoft.Xna.Framework.Graphics;
using System.Windows.Media.Imaging;
using System.IO.IsolatedStorage;

namespace _3DPresentation.Utils
{
    internal static class Global
    {
        public static string TourStorePath = "Tour";

        public static DirectoryInfo GetRealDirectory(string path)
        {
            DirectoryInfo dir = new DirectoryInfo(path);
            if (dir.Parent.Exists == false)
                GetRealDirectory(dir.Parent.FullName);
            if (dir.Exists == false)
                dir.Create();            
            return dir;
        }
        public static FileInfo GetRealFile(string path)
        {
            FileInfo file = new FileInfo(path);
            if (file.Directory.Exists == false)
                GetRealDirectory(file.Directory.FullName);
            if (file.Exists == false)
            {
                file.Create().Close();
            }
            return file;
        }
        public static FileInfo GetFileInfo(string path)
        {
            FileInfo file = new FileInfo(path);
            if (file.Directory.Exists == false)
                GetRealDirectory(file.Directory.FullName);
            return file;
        }

        public static Texture2D LoadTexture(string resource, GraphicsDevice graphicsDevice)
        {
            // MUST BE CALL ON MAIN THREAD (or UI THREAD) ---- cause new an BitmapImage element
            //var stream = Application.GetResourceStream(new Uri(resource, UriKind.Relative)).Stream;
            var stream = Utils.Global.GetPackStream(resource);
            if (stream == null)
                return null;

            var bmp = new BitmapImage();
            bmp.SetSource(stream);
            Texture2D res = new Texture2D(graphicsDevice, bmp.PixelWidth, bmp.PixelHeight, false, SurfaceFormat.Color);
            bmp.CopyTo(res);
            return res;
        }

        public static Stream GetPackStream(string path)
        {
            Stream stream = null;
            try
            {
                Uri uri = MakePackUri(path);
                stream = Application.GetResourceStream(uri).Stream;
            }
            catch (Exception ex)
            { stream = null; }
            return stream;
        }

        public static Stream GetPackStream(Uri uri)
        {
            return Application.GetResourceStream(uri).Stream;
        }

        public static Stream GetLocalStream(Uri uri)
        {
            Stream stream = null;
            if (uri.IsAbsoluteUri)
            {
                FileInfo file = new FileInfo(uri.LocalPath);
                if (file.Exists)
                    stream = file.OpenRead();
            }
            return stream;
        }

        public static Uri MakePackUri(string relativeFile)
        {
            string uriString = "/" + AssemblyShortName + ";component/" + relativeFile;
            Uri result = null;
            try
            {
                result = new Uri(uriString, UriKind.Relative);
            }
            catch (UriFormatException)
            {
                result = null;
            }
            return result;
        }

        //public static Uri MakeStoreUri(string relativeFile)
        //{
        //    string uriString = StorePath + '/' + relativeFile;
        //    Uri result = null;
        //    try
        //    {
        //        result = new Uri(uriString, UriKind.Absolute);
        //    }
        //    catch (UriFormatException)
        //    {
        //        result = null;
        //    }
        //    return result;
        //}

        public static Uri MakeRelativeUri(Uri baseUri, string relativeFile)
        {
            Uri result = null;
            string strBaseUri = baseUri.ToString();
            if (strBaseUri.Length > 2)
            {
                int lastSlash = strBaseUri.LastIndexOf('/', strBaseUri.Length - 2);
                strBaseUri = strBaseUri.Substring(0, lastSlash);

                try
                {
                    result = new Uri(strBaseUri + '/' + relativeFile, UriKind.RelativeOrAbsolute);
                }
                catch(UriFormatException ex)
                {
                    result = null;
                }
            }
            return result;
        }

        private static string _assemblyShortName;
        private static string AssemblyShortName
        {
            get
            {
                if (_assemblyShortName == null)
                {
                    Assembly a = typeof(Global).Assembly;

                    // Pull out the short name.
                    _assemblyShortName = a.ToString().Split(',')[0];
                }

                return _assemblyShortName;
            }
        }

		public static string GetRandomSnapshot()
        {

            string [] str = new string[] {
                "Views/Editor/Images/j0309223.jpg",
                "Views/Editor/Images/j0314069.jpg",
                "Views/Editor/Images/j0402444.jpg",
                "Views/Editor/Images/j0406500.jpg",
                "Views/Editor/Images/j0406702.jpg",
                "Views/Editor/Images/j0407544.jpg",
                "Views/Editor/Images/j0422769.jpg",
                "Views/Editor/Images/j0428653.jpg",
                "Views/Editor/Images/j0314059.jpg",
                "Views/Editor/Images/j0430836.jpg",
                "Views/Editor/Images/j0431767.jpg",
                "Views/Editor/Images/j0433157.jpg"
            };
            Random rd = new Random();
            return str[rd.Next(str.Length)];
        }

        private static void CreateDirs(IsolatedStorageFile store, string path)
        {
            if (path.Length == 0)
                return;
            if (store.DirectoryExists(path))
                return;
            CreateDirs(store, Path.GetDirectoryName(path));
            store.CreateDirectory(path);
        }

        public static Stream GetStream(string path, FileMode mode)
        {
            Stream result = null;
            using (var store = IsolatedStorageFile.GetUserStoreForApplication())
            {
                if (store.FileExists(path) == false)
                {
                    if (mode != FileMode.Open)
                    {                        
                        CreateDirs(store, Path.GetDirectoryName(path));
                        result = store.CreateFile(path);
                    }
                }
                else
                    result = store.OpenFile(path, mode);
            }
            return result;
        }
        public static bool WriteTo(string path, MemoryStream ms)
        {
            bool result = false;
            using (var store = IsolatedStorageFile.GetUserStoreForApplication())
            {
                long availableSpace = store.AvailableFreeSpace;
                long need = 0;
                Stream stream = null;
                if (store.FileExists(path))
                {
                    stream = store.OpenFile(path, FileMode.Open);
                    need = ms.Length - stream.Length;
                    stream.Close();
                }
                else
                    need = ms.Length;

                CreateDirs(store, Path.GetDirectoryName(path));
                stream = store.OpenFile(path, FileMode.Create);

                if (need - availableSpace > 0)
                {
                    if (IncreaseQuota())
                        ms.WriteTo(stream);
                    else
                        MessageBox.Show("Not enough free space in application's storage.");
                }
                else
                    ms.WriteTo(stream);

                stream.Flush();
                stream.Close();                
                result = true;
            }
            return result;
        }
        public static string[] GetTourList()
        {
            string[] tourList = null;
            using (var store = IsolatedStorageFile.GetUserStoreForApplication())
            {
                string path = Path.Combine(TourStorePath, "*.*");
                if (store.DirectoryExists(TourStorePath))
                    tourList = store.GetDirectoryNames(path);
                else
                    tourList = new string[0];
            }
            return tourList;
        }
        public static void DeleteAllTours()
        {
            using (var store = IsolatedStorageFile.GetUserStoreForApplication())
            {
                if (store.DirectoryExists(TourStorePath))
                {
                    DeleteDirectory(store, TourStorePath);
                }                
            }
        }
        private static void DeleteDirectory(IsolatedStorageFile store, string path)
        {
            string[] dirs = store.GetDirectoryNames(Path.Combine(path, "*"));
            foreach (string dir in dirs)
                DeleteDirectory(store, Path.Combine(path, dir));

            string[] files = store.GetFileNames(Path.Combine(path, "*.*"));
            foreach (string file in files)
                store.DeleteFile(Path.Combine(path, file));

            store.DeleteDirectory(path);
        }
        public static bool IncreaseQuota()
        {
            bool result = false;
            using (var store = IsolatedStorageFile.GetUserStoreForApplication())
            {
                result = store.IncreaseQuotaTo(store.Quota + 1048576 * 50);
            }
            return result;
        }
        public static bool IsFull()
        {
            bool result = false;
            using (var store = IsolatedStorageFile.GetUserStoreForApplication())
            {
                result = (store.AvailableFreeSpace == 0);
            }
            return result;
        }
    }
}
