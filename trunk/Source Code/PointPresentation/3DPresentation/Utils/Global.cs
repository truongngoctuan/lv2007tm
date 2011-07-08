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
        public static Texture2D LoadTexture(string resource, GraphicsDevice graphicsDevice)
        {
            // MUST BE CALL ON MAIN THREAD (or UI THREAD) ---- cause new an BitmapImage element
            //var stream = Application.GetResourceStream(new Uri(resource, UriKind.Relative)).Stream;
            var stream = Utils.Global.GetStream(resource);
            var bmp = new BitmapImage();
            bmp.SetSource(stream);
            Texture2D res = new Texture2D(graphicsDevice, bmp.PixelWidth, bmp.PixelHeight, false, SurfaceFormat.Color);
            bmp.CopyTo(res);
            return res;
        }

        public static Stream GetStream(string path)
        {
            Uri uri = MakePackUri(path);
            return Application.GetResourceStream(uri).Stream;
        }

        public static Stream GetStream(Uri uri)
        {
            return Application.GetResourceStream(uri).Stream;
        }

        public static Uri MakePackUri(string relativeFile)
        {
            string uriString = "/" + AssemblyShortName + ";component/" + relativeFile;
            return new Uri(uriString, UriKind.Relative);
        }

        public static Uri MakePackUri(Uri baseUri, string relativeFile)
        {
            Uri result = null;
            string strBaseUri = baseUri.ToString();
            if (strBaseUri.Length > 2)
            {
                int lastSlash = strBaseUri.LastIndexOf('/', strBaseUri.Length - 2);
                strBaseUri = strBaseUri.Substring(0, lastSlash);

                try
                {
                    result = new Uri(strBaseUri + '/' + relativeFile, UriKind.Relative);
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
    }
}
