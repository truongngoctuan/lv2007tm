using Microsoft.Xna.Framework.Graphics;
using Microsoft.Xna.Framework.Silverlight;
using System.Collections.Generic;
using System.Windows.Media.Imaging;
using System;
using System.IO;
using ImageTools;
using ImageTools.IO;



namespace _3DPresentation
{
    public class ResourceManager
    {
        private static readonly GraphicsDevice resourceDevice = GraphicsDeviceManager.Current.GraphicsDevice;
        private static Dictionary<string, Texture2D> Textures = new Dictionary<string,Texture2D>();
        private static Dictionary<Texture2D, BitmapImage> Bitmaps = new Dictionary<Texture2D, BitmapImage>();

        private static bool IsReady = false;
        public static void Init()
        {
            if (IsReady)
                return;
            Encoders.AddEncoder<ImageTools.IO.Jpeg.JpegEncoder>();
            Encoders.AddEncoder<ImageTools.IO.Png.PngEncoder>();
            IsReady = true;
        }

        private static List<string> AddedTexture = new List<string>();
        public static Texture2D GetTexture(string path)
        {
            try
            {
                if (path == null || path.Length == 0 || path == " ")
                    return null;
                if (Textures.ContainsKey(path))
                    return Textures[path];

                if (AddedTexture.Contains(path) == false)
                {
                    AddedTexture.Add(path);
                    App.CurrentPage.Dispatcher.BeginInvoke(new Action(() =>
                    {
                        Texture2D texture = Utils.Global.LoadTexture(path, resourceDevice);
                        Textures.Add(path, texture);
                    }));
                }
            }
            catch (Exception ex)
            { }
            return null;
        }

        public static BitmapImage LoadTexture(FileInfo textureFile, string key)
        {
            BitmapImage bmp = null;            
            try
            {
                if (Textures.ContainsKey(key))
                    return Bitmaps[Textures[key]];
                if (textureFile.Exists)
                {                    
                    FileStream stream = textureFile.OpenRead();
                    bmp = new BitmapImage();
                    bmp.SetSource(stream);

                    Texture2D res = new Texture2D(resourceDevice, bmp.PixelWidth, bmp.PixelHeight, false, SurfaceFormat.Color);
                    bmp.CopyTo(res);

                    Textures.Add(key, res);
                    Bitmaps.Add(res, bmp);
                }
            }
            catch (Exception ex)
            {
                bmp = null;
            }
            return bmp;
        }

        public static bool SaveBitmap(Texture2D texture2D, string filePath)
        {   
            bool result = false;
            if (Bitmaps.ContainsKey(texture2D))
            {
                BitmapImage bitmapImage = Bitmaps[texture2D];
                WriteableBitmap writableBitmap = new WriteableBitmap(bitmapImage);
                ExtendedImage myImage = ImageExtensions.ToImage(writableBitmap);
                FileInfo file = Utils.Global.GetRealFile(filePath);
                using (Stream stream = file.OpenWrite())
                {
                    myImage.WriteToStream(stream);
                    stream.Close();
                    result = true;
                }
                myImage = null;
                writableBitmap = null;
            }
            return result;
        }
        public static bool SaveBitmap(string key, string filePath)
        {
            if (key == null)
                return false;
            bool result = false;
            if (Textures.ContainsKey(key))
            {
                result = SaveBitmap(Textures[key], filePath);
            }
            return result;
        }
    }
}
