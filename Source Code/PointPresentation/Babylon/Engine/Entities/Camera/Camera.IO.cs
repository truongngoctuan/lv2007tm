using System.IO;

namespace Babylon
{
    public partial class Camera
    {
        internal void Load(BinaryReader reader)
        {
            ID = reader.ReadGuid();
            LoadedParentID = reader.ReadGuid();
            PositionRelativeToParent = reader.ReadVector3();

            bool hasTarget = reader.ReadBoolean();
            if (hasTarget)
                LoadedTargetID = reader.ReadGuid();
            else
                Rotation = reader.ReadVector3();

            FOV = reader.ReadSingle();
            NearClip = reader.ReadSingle();
            FarClip = reader.ReadSingle();
            NearPlane = reader.ReadSingle();
            FarPlane = reader.ReadSingle();

            Inertia = reader.ReadSingle();
            
            CheckCollisions = reader.ReadBoolean();
            IsFlying = !reader.ReadBoolean();
            Speed = reader.ReadSingle();
            Ellipsoid = reader.ReadVector3();
        }
    }
}
