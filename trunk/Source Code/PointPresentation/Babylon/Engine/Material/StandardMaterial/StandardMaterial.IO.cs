using System.IO;

namespace Babylon
{
    public partial class StandardMaterial
    {
        internal void Load(BinaryReader reader, bool streamMode)
        {
            ID = reader.ReadGuid();
            Alpha = reader.ReadSingle();
            HasTextureAlpha = reader.ReadBoolean();
            Ambient = reader.ReadColor();
            Diffuse = reader.ReadColor();
            Emissive = reader.ReadColor();
            SelfIllumination = reader.ReadSingle();
            Specular = reader.ReadColor();
            SpecularSharpness = reader.ReadSingle();

            // Diffuse texture
            if (reader.ReadBoolean())
            {
                DiffuseTexture = new Texture(reader.ReadString(), Scene);
                DiffuseTexture.Load(reader, streamMode);
            }

            // Ambient texture
            if (reader.ReadBoolean())
            {
                AmbientTexture = new Texture(reader.ReadString(), Scene);
                AmbientTexture.Load(reader, streamMode);
            }

            // Opacity texture
            if (reader.ReadBoolean())
            {
                OpacityTexture = new Texture(reader.ReadString(), Scene);
                OpacityTexture.Load(reader, streamMode);
            }
        }
    }
}
