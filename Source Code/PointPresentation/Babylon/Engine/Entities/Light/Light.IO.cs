using System.IO;

namespace Babylon
{
    public partial class Light
    {
        internal void Load(BinaryReader reader)
        {
            ID = reader.ReadGuid();
            LoadedParentID = reader.ReadGuid();
            Enabled = reader.ReadBoolean();
            Type = (LightType) reader.ReadInt32();
            PositionRelativeToParent = reader.ReadVector3();
            DirectionRelativeToParent = reader.ReadVector3();
            Diffuse = reader.ReadColor();
            Specular = reader.ReadColor();
        }
    }
}
