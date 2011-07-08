using System.IO;
using System;

namespace Babylon
{
    public class Logger
    {
        public static string FolderPath = Environment.GetFolderPath(Environment.SpecialFolder.MyDocuments);
        public static bool IsInitialized { get; set; }

        private static StreamWriter textWriter;
        public static void Init()
        {
            string path = FolderPath + "\\Log\\log.txt";
            //string[] lines = { "exit" };
            //System.IO.File.WriteAllLines(WorkingDirectoryTemp + "\\cm.txt", lines);
            FileInfo file = new FileInfo(path);
            if (file.Exists == false)
                textWriter = file.CreateText();
            else
                textWriter = new StreamWriter(file.Open(FileMode.Append, FileAccess.Write));

            textWriter.AutoFlush = true;
            IsInitialized = true;
        }
        public static void Write(string str)
        {
            if (IsInitialized == false)
                Init();

            textWriter.WriteLine(str);
        }
        public static void End()
        {
            textWriter.Flush();
            textWriter.Close();
            IsInitialized = false;
        }
    }
}
