using System;
using System.IO;
using System.Reflection;
using System.Windows;

namespace _3DPresentation.Utils
{
    internal static class Global
    {
        public static Stream GetStream(string path)
        {
            Uri uri = MakePackUri(path);
            return Application.GetResourceStream(uri).Stream;
        }

        public static Uri MakePackUri(string relativeFile)
        {
            string uriString = "/" + AssemblyShortName + ";component/" + relativeFile;
            return new Uri(uriString, UriKind.Relative);
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
