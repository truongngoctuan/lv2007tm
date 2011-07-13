using System;
using System.IO;
using System.Reflection;
using System.Windows;
using Microsoft.Xna.Framework.Graphics;
using System.Windows.Media.Imaging;

namespace _3DPresentation.Utils
{
    internal static class Global
    {
        public static string MyDocumentsFolderPath = Environment.GetFolderPath(Environment.SpecialFolder.MyDocuments);

        public static string StorePath = MyDocumentsFolderPath + '/' + "Silverlight3D/";
        public static string ModelStorePath = StorePath + "Model/";
        public static string SceneStorePath = StorePath + "Scene/";
        public static string TourStorePath = StorePath + "Tour/";

        public static string GetRealStoreDirectory()
        {
            DirectoryInfo dir = new DirectoryInfo(StorePath);
            if (dir.Exists == false)
                dir.Create();
            return StorePath;
        }

        public static string GetRealModelStoreDirectory()
        {
            GetRealStoreDirectory();
            DirectoryInfo dir = new DirectoryInfo(ModelStorePath);
            if (dir.Exists == false)
                dir.Create();
            return ModelStorePath;
        }

        public static string GetRealSceneStorePath()
        {
            GetRealStoreDirectory();
            DirectoryInfo dir = new DirectoryInfo(SceneStorePath);
            if (dir.Exists == false)
                dir.Create();
            return SceneStorePath;
        }

        public static string GetRealTourStorePath()
        {
            GetRealStoreDirectory();
            DirectoryInfo dir = new DirectoryInfo(TourStorePath);
            if (dir.Exists == false)
                dir.Create();
            return TourStorePath;
        }

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
            var bmp = new BitmapImage();
            bmp.SetSource(stream);
            Texture2D res = new Texture2D(graphicsDevice, bmp.PixelWidth, bmp.PixelHeight, false, SurfaceFormat.Color);
            bmp.CopyTo(res);
            return res;
        }

        public static Texture2D LoadLocalTexture(string relativePath, GraphicsDevice graphicsDevice)
        {
            // MUST BE CALL ON MAIN THREAD (or UI THREAD) ---- cause new an BitmapImage element
            //var stream = Application.GetResourceStream(new Uri(resource, UriKind.Relative)).Stream;
            Uri textureUri = Utils.Global.MakeStoreUri(relativePath);
            var stream = Utils.Global.GetLocalStream(textureUri);
            var bmp = new BitmapImage();
            bmp.SetSource(stream);
            Texture2D res = new Texture2D(graphicsDevice, bmp.PixelWidth, bmp.PixelHeight, false, SurfaceFormat.Color);
            bmp.CopyTo(res);
            return res;
        }

        public static Stream GetPackStream(string path)
        {
            Uri uri = MakePackUri(path);
            return Application.GetResourceStream(uri).Stream;
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

        public static Uri MakeStoreUri(string relativeFile)
        {
            string uriString = StorePath + '/' + relativeFile;
            Uri result = null;
            try
            {
                result = new Uri(uriString, UriKind.Absolute);
            }
            catch (UriFormatException)
            {
                result = null;
            }
            return result;
        }

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

        private static string _assemblyShortName;

        public static BitmapImage AbsolutePathStringToBitmapImage(string str)
        {
            BitmapImage bi = new BitmapImage();
            FileInfo fio = new FileInfo(str);
            System.IO.Stream stream2 = fio.OpenRead();
            bi.SetSource(stream2);
            stream2.Close();

            return bi;
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
    }
}
