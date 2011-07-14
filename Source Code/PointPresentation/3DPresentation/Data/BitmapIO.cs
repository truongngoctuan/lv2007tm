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
using System.Windows.Media.Imaging;

namespace _3DPresentation
{
    // Reference : http://www.codeproject.com/Articles/38636/Saving-Bitmaps-to-Isolated-Storage-in-Silverlight
    // Modified
    public class BitmapIO
    {
        public static BitmapImage LoadBitmap(FileInfo file)
        {
            byte[] bytes = _LoadIfExists(file);
            if (bytes.Length > 0)
            {
                #region http://social.msdn.microsoft.com/Forums/en/windowsphone7series/thread/8645414c-907b-462c-aa54-5b3b86b2a243
                WriteableBitmap wb = _GetImage(bytes);
                MemoryStream ms = new MemoryStream(); 
                //wb.LoadJpeg(//your image stream from IsolatedStorage);
                //wb.(ms, (int)image1.Width, (int)image1.Height, 0, 100);
                BitmapImage bmp = new BitmapImage();
                bmp.SetSource(ms);
                #endregion
            }
            return null;
        }
        public static bool SaveBitmap(BitmapImage bm, FileInfo file)
        {
            WriteableBitmap writableBitmap = new WriteableBitmap(bm);
            byte[] bytes = _GetSaveBuffer(writableBitmap);
            _SaveToDisk(bytes, file);
            return true;
        }

        private static byte[] _LoadIfExists(FileInfo file)
        {
            byte[] retVal;
            using (FileStream stream = file.OpenRead())
            {
                retVal = new byte[stream.Length];
                stream.Read(retVal, 0, retVal.Length);
            }            
            return retVal;
        }

        private static void _SaveToDisk(byte[] buffer, FileInfo fileName)
        {
            FileStream stream;
            if (fileName.Exists == false)
                stream = fileName.Create();
            else
                stream = fileName.OpenWrite();

            if (stream != null)
            {
                stream.Write(buffer, 0, buffer.Length);
                stream.Close();
            }
        }

        /// <summary>
        ///     Gets an image from storage
        /// </summary>
        /// <param name="buffer"></param>
        /// <returns>The bitmap</returns>
        public static WriteableBitmap _GetImage(byte[] buffer)
        {
            int width = buffer[0] * 256 + buffer[1];
            int height = buffer[2] * 256 + buffer[3];

            long matrixSize = width * height;

            WriteableBitmap retVal = new WriteableBitmap(width, height);

            int bufferPos = 4;

            for (int matrixPos = 0; matrixPos < matrixSize; matrixPos++)
            {
                int pixel = buffer[bufferPos++];
                pixel = pixel << 8 | buffer[bufferPos++];
                pixel = pixel << 8 | buffer[bufferPos++];
                pixel = pixel << 8 | buffer[bufferPos++];
                retVal.Pixels[matrixPos] = pixel;
            }

            return retVal;
        }

        /// <summary>
        ///     Gets the buffer to save to disk from the writeable bitmap
        /// </summary>
        /// <param name="bitmap">The bitmap image</param>
        /// <returns>The buffer of bytes</returns>
        private static byte[] _GetSaveBuffer(WriteableBitmap bitmap)
        {
            long matrixSize = bitmap.PixelWidth * bitmap.PixelHeight;

            long byteSize = matrixSize * 4 + 4;

            byte[] retVal = new byte[byteSize];

            long bufferPos = 0;

            retVal[bufferPos++] = (byte)((bitmap.PixelWidth / 256) & 0xff);
            retVal[bufferPos++] = (byte)((bitmap.PixelWidth % 256) & 0xff);
            retVal[bufferPos++] = (byte)((bitmap.PixelHeight / 256) & 0xff);
            retVal[bufferPos++] = (byte)((bitmap.PixelHeight % 256) & 0xff);

            for (int matrixPos = 0; matrixPos < matrixSize; matrixPos++)
            {
                retVal[bufferPos++] = (byte)((bitmap.Pixels[matrixPos] >> 24) & 0xff);
                retVal[bufferPos++] = (byte)((bitmap.Pixels[matrixPos] >> 16) & 0xff);
                retVal[bufferPos++] = (byte)((bitmap.Pixels[matrixPos] >> 8) & 0xff);
                retVal[bufferPos++] = (byte)((bitmap.Pixels[matrixPos]) & 0xff);
            }

            return retVal;
        }
    }
}
