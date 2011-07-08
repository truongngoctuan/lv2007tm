using System;
using System.Collections.Generic;
using System.IO;
using System.Windows.Controls;
using System.Windows.Media;
using Microsoft.Xna.Framework.Graphics;
using System.Windows.Media.Imaging;
using Babylon.Toolbox;

namespace Babylon
{
    public partial class Engine
    {
        readonly Dictionary<string, LoadedTexture> loadedTextures = new Dictionary<string, LoadedTexture>();

        public LoadedTexture PreLoadTexture(BinaryReader reader, string name, bool hasAlpha)
        {
            LoadedTexture loadedTexture;

            if (!loadedTextures.TryGetValue(name, out loadedTexture))
            {
                int streamID = reader.ReadInt32();

                loadedTexture = new LoadedTexture(name, hasAlpha, streamID, this);
                loadedTextures.Add(name, loadedTexture);
            }

            loadedTexture.Reference++;

            return loadedTexture;
        }

        public LoadedTexture LoadTexture(BinaryReader reader, string name, bool hasAlpha)
        {
            LoadedTexture loadedTexture;

            if (!loadedTextures.TryGetValue(name, out loadedTexture))
            {
                Texture2D texture2D = LoadTexture2D(reader, hasAlpha);

                if (texture2D == null)
                    return null;

                loadedTexture = new LoadedTexture(name, texture2D, hasAlpha, this);
                
                loadedTextures.Add(name, loadedTexture);
            }

            loadedTexture.Reference++;

            return loadedTexture;
        }

        internal Texture2D LoadTexture2D(BinaryReader reader, bool hasAlpha)
        {
            int size = reader.ReadInt32();
            if (size == 0)
                return null;

            byte[] datas = reader.ReadBytes(size);
            
            Texture2D texture2D = null;

            SynchronizationContext.Send(o =>
                                            {
                                                using (MemoryStream memoryStream = new MemoryStream(datas))
                                                {
                                                    texture2D = ContentManager.LoadTexture2D(Device, memoryStream, !hasAlpha);
                                                }
                                            }, null);

            return texture2D;
        }

        public void Dispose()
        {
            foreach (LoadedTexture loadedTexture in loadedTextures.Values)
            {
                loadedTexture.Dispose();
            }

            loadedTextures.Clear();
        }

        internal void ReleaseTexture(LoadedTexture loadedTexture)
        {
            if (loadedTexture == null)
                return;

            loadedTexture.Reference--;

            if (loadedTexture.Reference == 0)
            {
                loadedTextures.Remove(loadedTexture.Name);
                loadedTexture.Dispose();
            }
        }
    }
}
