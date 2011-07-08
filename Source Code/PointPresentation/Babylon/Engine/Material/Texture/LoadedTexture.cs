using System;
using System.IO;
using Microsoft.Xna.Framework.Graphics;
using System.Diagnostics;

namespace Babylon
{
    public class LoadedTexture : IDisposable, IStreamableData
    {
        Texture2D texture;
        readonly string name;
        readonly Engine engine;

        public int StreamID { get; private set; }

        internal LoadedTexture(string name, bool hasAlpha, int dataStreamID, Engine scene)
        {
            this.engine = scene;
            StreamID = dataStreamID;
            HasAlpha = hasAlpha;
            this.name = name;
            StreamingState = StreamingState.PreLoaded;
        }

        internal LoadedTexture(string name, Texture2D texture, bool hasAlpha, Engine scene)
        {
            this.engine = scene;
            HasAlpha = hasAlpha;
            this.name = name;
            this.texture = texture;
            StreamingState = StreamingState.Loaded;
        }

        public Texture2D Texture2D
        {
            get { return texture; }
        }

        public StreamingState StreamingState { get; set; }

        public int Reference { get; internal set; }

        public string Name
        {
            get { return name; }
        }

        public bool HasAlpha { get; set; }

        public void Dispose()
        {
        //    texture.Dispose();
        }

        public void ProcessStream(Stream stream)
        {
            using (BinaryReader reader = new BinaryReader(stream))
            {
                texture = engine.LoadTexture2D(reader, HasAlpha);
            }
            StreamingState = StreamingState.Loaded;
        }
    }
}