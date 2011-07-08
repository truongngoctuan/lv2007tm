using Microsoft.Xna.Framework;

namespace Babylon
{
    internal class CollisionPlane
    {
        internal Vector3 origin;
        internal Vector3 normal;
        readonly float[] equation = new float[4];

        public CollisionPlane(Vector3 origin, Vector3 normal)
        {
            this.normal = normal;
            this.origin = origin;

            normal.Normalize();

            equation[0] = normal.X;
            equation[1] = normal.Y;
            equation[2] = normal.Z;
            equation[3] = -(normal.X * origin.X + normal.Y * origin.Y + normal.Z * origin.Z);
        }

        public CollisionPlane(Vector3 p1, Vector3 p2, Vector3 p3)
        {
            normal = Vector3.Cross(p2 - p1, p3 - p1);
            origin = p1;

            normal.Normalize();

            equation[0] = normal.X;
            equation[1] = normal.Y;
            equation[2] = normal.Z;
            equation[3] = -(normal.X * origin.X + normal.Y * origin.Y + normal.Z * origin.Z);
        }

        public bool IsFrontFacingTo(Vector3 direction, float epsilon)
        {
            double dot = Vector3.Dot(normal, direction);

            return (dot <= epsilon);
        }

        public float SignedDistanceTo(Vector3 point)
        {
            return Vector3.Dot(point, normal) + equation[3];
        }
    }
}
