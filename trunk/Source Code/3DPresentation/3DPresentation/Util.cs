using System;
using System.Net;
using System.Windows;
using System.Windows.Controls;
using System.Windows.Documents;
using System.Windows.Ink;
using System.Windows.Input;
using System.Windows.Media;
using System.Windows.Media.Animation;
using System.Windows.Shapes;
using System.IO;

namespace _3DPresentation
{
    public class Util
    {
        public static Stream GetStream(string assembly, string path)
        {
            string uri = string.Format(@"/{0};component/{1}", assembly, path);
            return Application.GetResourceStream(new Uri(uri, UriKind.Relative)).Stream;
        }
    }
}
