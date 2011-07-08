using Microsoft.Xna.Framework;
using BoundingBox = Babylon.Maths.BoundingBox;
using BoundingSphere = Babylon.Maths.BoundingSphere;

namespace Babylon
{
    public class BoundingInfo
    {   
        public BoundingBox BoundingBox;
        internal Vector3[] BoundingBoxVectors = new Vector3[8];
        internal Vector3[] boundingBoxVectorsWorld = new Vector3[8];
        public BoundingSphere BoundingSphere;
        public Vector3 MinBoxWorld;
        public Vector3 MaxBoxWorld;
        public Vector3 SphereCenterWorld;
        public float SphereRadiusWorld;

        public BoundingInfo(Vector3[] points)
        {
            BoundingBox = BoundingBox.FromPoints(points);
            BoundingSphere = BoundingSphere.FromPoints(points);
            Construct();
        }

        internal void Construct()
        {
            BoundingBoxVectors[0] = BoundingBox.Minimum;
            BoundingBoxVectors[1] = BoundingBox.Maximum;

            BoundingBoxVectors[2] = BoundingBox.Minimum;
            BoundingBoxVectors[2].X = BoundingBox.Maximum.X;

            BoundingBoxVectors[3] = BoundingBox.Minimum;
            BoundingBoxVectors[3].Y = BoundingBox.Maximum.Y;

            BoundingBoxVectors[4] = BoundingBox.Minimum;
            BoundingBoxVectors[4].Z = BoundingBox.Maximum.Z;

            BoundingBoxVectors[5] = BoundingBox.Maximum;
            BoundingBoxVectors[5].Z = BoundingBox.Minimum.Z;

            BoundingBoxVectors[6] = BoundingBox.Maximum;
            BoundingBoxVectors[6].X = BoundingBox.Minimum.X;

            BoundingBoxVectors[7] = BoundingBox.Maximum;
            BoundingBoxVectors[7].Y = BoundingBox.Minimum.Y;
        }

        public void UpdateWorldDatas(Matrix world, float scale)
        {
            Vector3.Transform(BoundingBoxVectors, ref world, boundingBoxVectorsWorld);
            MinBoxWorld = new Vector3(float.MaxValue, float.MaxValue, float.MaxValue);
            MaxBoxWorld = new Vector3(float.MinValue, float.MinValue, float.MinValue);

            foreach (Vector3 v in boundingBoxVectorsWorld)
            {
                if (v.X < MinBoxWorld.X)
                    MinBoxWorld.X = v.X;
                if (v.Y < MinBoxWorld.Y)
                    MinBoxWorld.Y = v.Y;
                if (v.Z < MinBoxWorld.Z)
                    MinBoxWorld.Z = v.Z;

                if (v.X > MaxBoxWorld.X)
                    MaxBoxWorld.X = v.X;
                if (v.Y > MaxBoxWorld.Y)
                    MaxBoxWorld.Y = v.Y;
                if (v.Z > MaxBoxWorld.Z)
                    MaxBoxWorld.Z = v.Z;
            }

            SphereCenterWorld = Vector3.Transform(BoundingSphere.Center, world);

            SphereRadiusWorld = BoundingSphere.Radius * scale;
        }

        internal bool CheckCollision(CollisionSystem collider)
        {
            return collider.CanDoCollision(SphereCenterWorld, SphereRadiusWorld, MinBoxWorld, MaxBoxWorld);
        }
    }
}
