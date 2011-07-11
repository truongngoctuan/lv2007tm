﻿using System;
using System.Net;
using System.Windows;
using System.Windows.Controls;
using System.Windows.Documents;
using System.Windows.Ink;
using System.Windows.Input;
using System.Windows.Media;
using System.Windows.Media.Animation;
using System.Windows.Shapes;
using System.Runtime.InteropServices.Automation;
using System.Threading;
using System.Windows.Threading;
using System.IO;

namespace _3DPresentation.Utils
{
    public class COMAutomation
    {
        public static void Cmd(string strQuery)
        {
            using (dynamic shell = AutomationFactory.CreateObject("WScript.Shell"))
            {
                shell.Run(strQuery);
            }
        }

        public event EventHandler CreateFileEvent;
        public event EventHandler DeleteFileEvent;
        string _FileName = string.Empty;

        public string FileName
        {
            get { return _FileName; }
            set { _FileName = value; }
        }
        public void FolderListener(string strWatchFolder)
        {
            try
            {
                new Thread(() =>
                {
                    try
                    {
                        using (dynamic SWbemLocator = AutomationFactory.CreateObject("WbemScripting.SWbemLocator"))
                        {
                            SWbemLocator.Security_.ImpersonationLevel = 3;
                            SWbemLocator.Security_.AuthenticationLevel = 4;
                            dynamic IService = SWbemLocator.ConnectServer(".", @"root\cimv2");

                            string fileSystemWatcherQuery =
                                string.Format(@"SELECT * FROM __InstanceOperationEvent WITHIN 3 WHERE Targetinstance ISA 'CIM_DirectoryContainsFile' and TargetInstance.GroupComponent= 'Win32_Directory.Name=""{0}""'",
                                strWatchFolder);
                            dynamic monitor = IService.ExecNotificationQuery(fileSystemWatcherQuery);

                            while (true)
                            {
                                dynamic eventObject = monitor.NextEvent();
                                string eventType = eventObject.Path_.Class;
                                string path = eventObject.TargetInstance.PartComponent;

                                string[] strSplit = path.Split('\"');
                                FileName = strSplit[strSplit.Length - 2];
                                if (eventType.IndexOf("CreationEvent") > 0)
                                {
                                    CreateFileEvent(this, new EventArgs());
                                    continue;
                                }

                                if (eventType.IndexOf("DeletionEvent") > 0)
                                {
                                    DeleteFileEvent(this, new EventArgs());
                                    continue;
                                }
                            }
                        }
                    }
                    catch (Exception ex)
                    {
                        MessageBox.Show(ex.Message);
                        throw;
                    }

                }).Start();
            }
            catch (Exception ex)
            {
                MessageBox.Show(ex.Message);
                throw;
            }
        }

        public static void StopCommand(string strFileName, string strFileNameTemp, string[] cm)
        {//stop c++ exe
            try
            {
                System.IO.File.WriteAllLines(strFileNameTemp, cm);
                ClientFileAndDirectory.MoveFile(strFileNameTemp, strFileName);
            }
            catch (Exception ex)
            {
                MessageBox.Show(ex.Message);
                throw;
            }

        }
    }
}