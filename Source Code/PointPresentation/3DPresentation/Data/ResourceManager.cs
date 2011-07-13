using Microsoft.Xna.Framework.Graphics;
using Microsoft.Xna.Framework.Silverlight;
using System.Collections.Generic;
using System.Windows.Media.Imaging;
using System;
using System.IO;

namespace _3DPresentation
{
    public class ResourceManager
    {
        private static readonly GraphicsDevice resourceDevice = GraphicsDeviceManager.Current.GraphicsDevice;
        private static Dictionary<string, Texture2D> Textures = new Dictionary<string,Texture2D>();
        private static Dictionary<Texture2D, BitmapImage> Bitmaps = new Dictionary<Texture2D, BitmapImage>();
        public static Texture2D GetTexture(string path)
        {
            try
            {
                if (path == null)
                    return null;
                if (Textures.ContainsKey(path))
                    return Textures[path];

                Texture2D texture = Utils.Global.LoadTexture(path, resourceDevice);
                Textures.Add(path, texture);
                return Textures[path];
            }
            catch (Exception ex)
            { }
            return null;
        }

        public static Texture2D GetModelTexture(string tour, string model, string texture)
        {
            try
            {
                string relativePath = string.Format("/Tour/{0}/Models/{1}/{2}", tour, model, texture);
                if (Textures.ContainsKey(relativePath))
                    return Textures[relativePath];

                Uri textureUri = Utils.Global.MakeStoreUri(relativePath);
                var stream = Utils.Global.GetLocalStream(textureUri);
                var bmp = new BitmapImage();
                bmp.SetSource(stream);
                Texture2D res = new Texture2D(resourceDevice, bmp.PixelWidth, bmp.PixelHeight, false, SurfaceFormat.Color);
                bmp.CopyTo(res);

                Textures.Add(relativePath, res);
                Bitmaps.Add(res, bmp);
                return Textures[relativePath];
            }
            catch (Exception ex)
            { }
            return null;
        }

        public static bool SaveBitmap(Texture2D texture2D, string filePath)
        {
            bool result = false;
            if (Bitmaps.ContainsKey(texture2D))
            {
                FileInfo file = Utils.Global.GetRealFile(filePath);
                result = BitmapIO.SaveBitmap(Bitmaps[texture2D], file);
            }
            return result;
        }
        public static bool SaveBitmap(string key, string filePath)
        {
            bool result = false;
            if (Textures.ContainsKey(key))
            {
                result = SaveBitmap(Textures[key], filePath);
            }
            return result;
        }

        public static BitmapImage LoadTexture(FileInfo textureFile, string key)
        {
            BitmapImage bmp = null;
            try
            {
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
    }
}
