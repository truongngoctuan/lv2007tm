using Microsoft.Xna.Framework;

namespace _3DPresentation
{
    public class CustomBoundingInfo : Babylon.BoundingInfo
    {
        public BoundingBox BoundingBoxWorld { get; private set; }
        public BoundingSphere BoundingSphereWorld { get; private set; }

        public CustomBoundingInfo(Vector3[] points)
            : base(points)
        {
            BoundingBoxWorld = new BoundingBox(BoundingBox.Minimum, BoundingBox.Maximum);
            BoundingSphereWorld = new BoundingSphere(BoundingSphere.Center, BoundingSphere.Radius);
        }

        public new void UpdateWorldDatas(Matrix world, float scale)
        {
            base.UpdateWorldDatas(world, scale);

            BoundingBoxWorld = new BoundingBox(MinBoxWorld, MaxBoxWorld);
            BoundingSphereWorld = new BoundingSphere(SphereCenterWorld, SphereRadiusWorld);
        }
    }
}
