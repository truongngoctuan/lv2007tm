using System;
using System.IO;
using System.Net;
using System.Runtime.InteropServices.Automation;
using System.Windows;
using System.Windows.Controls;
using System.Windows.Documents;
using System.Windows.Ink;
using System.Windows.Input;
using System.Windows.Media;
using System.Windows.Media.Animation;
using System.Windows.Shapes;
using SharpGIS;

namespace _3DPresentation
{
    public class ClientFileAndDirectory
    {//http://justinangel.net/CuttingEdgeSilverlight4ComFeatures
        //using (dynamic fsoCom = AutomationFactory.CreateObject("Scripting.FileSystemObject"))
        //{
        //    dynamic file = fsoCom.OpenTextFile(@"c:\test.txt", 1, true);
        //    MessageBox.Show(file.ReadAll());
        //    file.Close();
        //}

        public static bool FileExists(string strFolderName)
        {
            using (dynamic fsoCom = AutomationFactory.CreateObject("Scripting.FileSystemObject"))
            {
                return fsoCom.FileExists(strFolderName);
            }
        }

        public static bool FolderExists(string strFolderName)
        {
            using (dynamic fsoCom = AutomationFactory.CreateObject("Scripting.FileSystemObject"))
            {
                return fsoCom.FolderExists(strFolderName);
            }
        }

        public static void CreateFolder(string strFolderName)
        {
            using (dynamic fsoCom = AutomationFactory.CreateObject("Scripting.FileSystemObject"))
            {
                fsoCom.CreateFolder(strFolderName);
            }
        }

        public static void DeleteFolder(string strFolderName)
        {
            using (dynamic fsoCom = AutomationFactory.CreateObject("Scripting.FileSystemObject"))
            {
                dynamic flr = fsoCom.GetFolder(strFolderName);
                fsoCom.DeleteFolder(flr);
            }
        }

        public static void DeleteFile(string strFolderName)
        {
            using (dynamic fsoCom = AutomationFactory.CreateObject("Scripting.FileSystemObject"))
            {
                dynamic fl = fsoCom.GetFile(strFolderName);
                fsoCom.DeleteFile(fl);
            }
        }

        public static void MoveFile(string strSource, string strDes)
        {
            using (dynamic fsoCom = AutomationFactory.CreateObject("Scripting.FileSystemObject"))
            {
                fsoCom.MoveFile(strSource, strDes);
            }
        }

        private static void ReadWriteStream(Stream readStream, Stream writeStream)
        {
            int Length = 256;
            Byte[] buffer = new Byte[Length];
            int bytesRead = readStream.Read(buffer, 0, Length);
            // write the required bytes
            while (bytesRead > 0)
            {
                writeStream.Write(buffer, 0, bytesRead);
                bytesRead = readStream.Read(buffer, 0, Length);
            }
            readStream.Close();
            writeStream.Close();
        }

        public static void UnZip(string strWorkingDirectory, Stream sUnzip)
        {
            try
            {
                strWorkingDirectory += "\\";
                UnZipper unzip = new UnZipper(sUnzip);
                    //string str = string.Empty;
                    //str += "___DIRECTORIES:___\n";
                    foreach (string filename in unzip.DirectoriesInZip)
                    {
                        //str += filename + "\n";
                        if (ClientFileAndDirectory.FolderExists(strWorkingDirectory + filename))
                        {
                            ClientFileAndDirectory.DeleteFolder(strWorkingDirectory + filename);
                        }
                        ClientFileAndDirectory.CreateFolder(strWorkingDirectory + filename);
                    }

                    //str += "___FILES:___\n";
                    foreach (string filename in unzip.FileNamesInZip)
                    {
                        //str += filename + "\n";
                        if (ClientFileAndDirectory.FileExists(strWorkingDirectory + filename))
                        {
                            ClientFileAndDirectory.DeleteFile(strWorkingDirectory + filename);
                        }
                        Stream stream = unzip.GetFileStream(filename);
                        string saveTo = strWorkingDirectory + filename;
                        // create a write stream
                        FileStream writeStream = new FileStream(saveTo, FileMode.Create, FileAccess.Write);
                        // write to the stream
                        ReadWriteStream(stream, writeStream);
                        writeStream.Close();

                    }
                    //MessageBox.Show(str);

            }
            catch (Exception ex)
            {
                MessageBox.Show(ex.Message);
                throw;
            }
        }
    }
}
