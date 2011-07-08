using System;
using System.Globalization;
using Microsoft.Xna.Framework;

namespace Babylon.Maths
{
    public struct BoundingSphere
    {
        public Vector3 Center;
        public float Radius;

        public BoundingSphere(Vector3 center, float radius)
        {
            Center = center;
            Radius = radius;
        }

        public static BoundingSphere FromPoints(Vector3[] points)
        {
            float radius;
            Vector3 center;
            BoundingSphere sphere;
            Vector3 maxX;
            Vector3 minY;
            Vector3 maxY;
            Vector3 minZ;
            Vector3 maxZ;
            if (points == null)
            {
                throw new ArgumentNullException("points");
            }
            Vector3 minX = maxX = minY = maxY = minZ = maxZ =points[0];
            foreach (Vector3 vector in points)
            {
                if (vector.X < minX.X)
                {
                    minX = vector;
                }
                if (vector.X > maxX.X)
                {
                    maxX = vector;
                }
                if (vector.Y < minY.Y)
                {
                    minY = vector;
                }
                if (vector.Y > maxY.Y)
                {
                    maxY = vector;
                }
                if (vector.Z < minZ.Z)
                {
                    minZ = vector;
                }
                if (vector.Z > maxZ.Z)
                {
                    maxZ = vector;
                }
            }
            float distanceX = Vector3.Distance(maxX, minX);
            float distanceY = Vector3.Distance(maxY, minY);
            float distanceZ = Vector3.Distance(maxZ, minZ);
            if (distanceX > distanceY)
            {
                if (distanceX > distanceZ)
                {
                    center = Vector3.Lerp(maxX, minX, 0.5f);
                    radius = distanceX * 0.5f;
                }
                else
                {
                    center = Vector3.Lerp(maxZ, minZ, 0.5f);
                    radius = distanceZ * 0.5f;
                }
            }
            else if (distanceY > distanceZ)
            {
                center = Vector3.Lerp(maxY, minY, 0.5f);
                radius = distanceY * 0.5f;
            }
            else
            {
                center = Vector3.Lerp(maxZ, minZ, 0.5f);
                radius = distanceZ * 0.5f;
            }
            foreach (Vector3 vector in points)
            {
                Vector3 temp;
                temp.X = vector.X - center.X;
                temp.Y = vector.Y - center.Y;
                temp.Z = vector.Z - center.Z;
                float currentRadius = temp.Length();
                if (currentRadius > radius)
                {
                    radius = (radius + currentRadius) * 0.5f;
                    center += (1f - (radius / currentRadius)) * temp;
                }
            }
            sphere.Center = center;
            sphere.Radius = radius;
            return sphere;

        }

        public static bool operator ==(BoundingSphere left, BoundingSphere right)
        {
            return Equals(left, right);
        }

        public static bool operator !=(BoundingSphere left, BoundingSphere right)
        {
            return !Equals(left, right);
        }

        public override string ToString()
        {
            return string.Format(CultureInfo.CurrentCulture, "Center:{0} Radius:{1}", Center, Radius);
        }

        public override int GetHashCode()
        {
            return Center.GetHashCode() + Radius.GetHashCode();
        }

        public override bool Equals(object value)
        {
            if (value == null)
                return false;

            if (value.GetType() != GetType())
                return false;

            return Equals((BoundingSphere)value);
        }

        public bool Equals(BoundingSphere value)
        {
            return (Center == value.Center && Radius == value.Radius);
        }
    }
}
