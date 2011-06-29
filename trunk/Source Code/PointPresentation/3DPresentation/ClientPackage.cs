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

namespace _3DPresentation
{
    public class ClientPackage
    {
        private string _strWorkingDirectory;

        public string WorkingDirectory
        {
            get { return _strWorkingDirectory; }
            set { _strWorkingDirectory = value; }
        }

        public void DownloadtoClient(string strPackageUri, string strWorkingDirectory)
        {
            //http://www.developerfusion.com/code/4669/save-a-stream-to-a-file/
            //http://www.sharpgis.net/post/2010/08/25/REALLY-small-unzip-utility-for-Silverlight-e28093-Part-2.aspx
            WebClient client = new WebClient();

            client.DownloadProgressChanged += client_DownloadProgressChanged;
            client.OpenReadCompleted += client_OpenReadCompleted;
            Uri ur = Application.Current.Host.Source;
            int a = ur.AbsolutePath.LastIndexOf('/');
            string asd1 = ur.AbsolutePath.Substring(0, a);
            string asd = asd1 + strPackageUri;

            WorkingDirectory = strWorkingDirectory;

            client.OpenReadAsync(new Uri(asd, UriKind.Relative));
        }

        //private decimal _megaBytesReceived;
        //private decimal _totalMegaBytes;
        void client_DownloadProgressChanged(object sender, DownloadProgressChangedEventArgs e)
        {
            //_megaBytesReceived = e.BytesReceived / 1024m / 1024m;
            //_totalMegaBytes = e.TotalBytesToReceive / 1024m / 1024m;
            //_megaBytesReceived = Math.Round(_megaBytesReceived, 3);
            //_totalMegaBytes = Math.Round(_totalMegaBytes, 3);
            //txtMegabytes.Text = string.Format("{0} von {1}", _megaBytesReceived, _totalMegaBytes);
            //progressBar.Value = e.ProgressPercentage;
        }

        void client_OpenReadCompleted(object sender, OpenReadCompletedEventArgs e)
        {

            if (e.Error != null)
            {
                // TODO: Fehler anzeigen
            }
            else
            {
                ClientFileAndDirectory.UnZip(WorkingDirectory, e.Result);
            }
        }
    }
}
