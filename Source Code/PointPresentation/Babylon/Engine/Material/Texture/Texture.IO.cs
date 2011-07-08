using System.IO;
using Microsoft.Xna.Framework.Graphics;

namespace Babylon
{
    public partial class Texture
    {
        internal void Load(BinaryReader reader, bool streamMode)
        {
            NeedInverseY = reader.ReadBoolean();
            UOffset = reader.ReadSingle();
            VOffset = reader.ReadSingle();
            UScale = reader.ReadSingle();
            VScale = reader.ReadSingle();
            UAng = reader.ReadSingle();
            VAng = reader.ReadSingle();
            WAng = reader.ReadSingle();

            UAddressMode = (TextureAddressMode)reader.ReadInt32();
            VAddressMode = (TextureAddressMode)reader.ReadInt32();

            MapCoordinatesIndex = reader.ReadInt32();

            Level = reader.ReadSingle();

            HasAlpha = reader.ReadBoolean();

            loadedTexture = !streamMode ? scene.Engine.LoadTexture(reader, Name, HasAlpha) : scene.Engine.PreLoadTexture(reader, Name, HasAlpha);

            if (streamMode && loadedTexture.Reference == 1)
                scene.ItemsToStream++;
        }
    }
}
