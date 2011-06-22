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
using System.Windows.Media.Imaging;
using System.Windows.Shapes;
using System.Runtime.InteropServices;
using System.Security;
using System.IO;
using System.Threading;
using System.Runtime.InteropServices.Automation;
namespace SilverlightApplication1
{
    public partial class MainPage : UserControl
    {
        public MainPage()
        {
            InitializeComponent();
        }

        public struct MyStruct
        {
            public int SomeId;
            public double SomePrice;
        }

        [SecuritySafeCritical]
        [DllImport(@"d:\\asd.DLL")]
        public static extern void PassStructIn(ref MyStruct theStruct);

        [SecuritySafeCritical]
        private void Button_Click(object sender, RoutedEventArgs e)
        {
            //MyStruct myStruct;
            //myStruct.SomeId = 23;
            //myStruct.SomePrice = 30.52;
            //PassStructIn(ref myStruct);
            try
            {
                MyStruct myStruct = asd();

                tb1.Text = myStruct.SomeId.ToString();
                tb2.Text = myStruct.SomePrice.ToString();

            }
            catch (Exception ex)
            {
                MessageBox.Show(ex.Message);
            }
        }
         public static MyStruct asd()
        {
            MyStruct myStruct;
            myStruct.SomeId = 23;
            myStruct.SomePrice = 30.52;
            PassStructIn(ref myStruct);

            return myStruct;
        }

         private void Button_Click_1(object sender, RoutedEventArgs e)
         {
             // check if we can actually do this
             if (!Application.Current.HasElevatedPermissions)
             {
                 MessageBox.Show("Application requires elevated trust for this!");
                 return;
             }

             // create a directory if necessary
             var tempDirectory = @"c:\temp";
             if (!Directory.Exists(tempDirectory))
             {
                 Directory.CreateDirectory(tempDirectory);
             }

             // build the full filename
             Random _rnd = new Random();
             var filename = string.Format("tempFile-{0}.txt", _rnd.Next(0, 65536));
             var fullPath = System.IO.Path.Combine(tempDirectory, filename);

             // write a new file
             using (FileStream fs = File.Create(fullPath))
             using (StreamWriter sr = new StreamWriter(fs, System.Text.Encoding.UTF8))
             {
                 sr.WriteLine("Hallo from a trusted app!");
             }

             // Notify the user
             MessageBox.Show("File has been created.");
         }

         private void Button_Click_2(object sender, RoutedEventArgs e)
         {
             new Thread(() =>
            {
                using (dynamic SWbemLocator = AutomationFactory.CreateObject("WbemScripting.SWbemLocator"))
                {
                    SWbemLocator.Security_.ImpersonationLevel = 3;
                    SWbemLocator.Security_.AuthenticationLevel = 4;
                    dynamic IService = SWbemLocator.ConnectServer(".", @"root\cimv2");


                    string fileSystemWatcherQuery =
                        @"SELECT * FROM __InstanceOperationEvent WITHIN 3 WHERE Targetinstance ISA 'CIM_DirectoryContainsFile' and TargetInstance.GroupComponent= 'Win32_Directory.Name=""d:\\\\test""'";
                    dynamic monitor = IService.ExecNotificationQuery(fileSystemWatcherQuery);

                    Dispatcher.BeginInvoke(() => MessageBox.Show(@"Now listening to file changes on d:\test"));

                    while (true)
                    {
                        dynamic eventObject = monitor.NextEvent();
                        string eventType = eventObject.Path_.Class;
                        string path = eventObject.TargetInstance.PartComponent;
                        
                        Dispatcher.BeginInvoke(() => {
                            //MessageBox.Show(eventType + ": " + path);
                            string[] strSplit = path.Split('\"');
                            //MessageBox.Show(eventType + ": " + strSplit[strSplit.Length - 2]);
                                                         string strFileName = strSplit[strSplit.Length - 2];
                            if(eventType.IndexOf("CreationEvent") > 0)
                            {
                                //create event
                                //MessageBox.Show("Create" + ": " + strFileName);

                                BitmapImage bi = new BitmapImage();
                                FileInfo fio = new FileInfo(strFileName);
                                System.IO.Stream stream2 = fio.OpenRead();
                                bi.SetSource(stream2);
                                myImage.Source = bi;
                                stream2.Close();

                                return;
                            }

                            if(eventType.IndexOf("DeletionEvent") > 0)
                            {
                                //delete event
                                MessageBox.Show("Delete" + ": " + strFileName);
                                return;
                            }
                        });
                    }
                }
            }).Start();
         }
    }
}
