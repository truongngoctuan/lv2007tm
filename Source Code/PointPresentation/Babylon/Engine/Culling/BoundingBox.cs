using System;
using System.Globalization;
using Microsoft.Xna.Framework;

namespace Babylon.Maths
{
    public struct BoundingBox
    {
        public Vector3 Maximum;
        public Vector3 Minimum;

        public BoundingBox(Vector3 minimum, Vector3 maximum)
        {
            Maximum = maximum;
            Minimum = minimum;
        }

        public static BoundingBox FromPoints(Vector3[] points)
        {
            if (points == null || points.Length <= 0)
                throw new ArgumentNullException("points");

            Vector3 min = new Vector3(float.MaxValue);
            Vector3 max = new Vector3(float.MinValue);

            foreach (Vector3 vector in points)
            {
                min = Vector3.Min(min, vector);
                max = Vector3.Max(max, vector);
            }

            return new BoundingBox(min, max);
        }

        public static bool Intersects( BoundingBox box, BoundingSphere sphere )
        {
            Vector3 clamped = Vector3.Clamp( sphere.Center, box.Minimum, box.Maximum );

			float x = sphere.Center.X - clamped.X;
			float y = sphere.Center.Y - clamped.Y;
			float z = sphere.Center.Z - clamped.Z;

			float dist = (x * x) + (y * y) + (z * z);

			return ( dist <= (sphere.Radius * sphere.Radius) );
        }

        public static bool operator ==(BoundingBox left, BoundingBox right)
        {
            return Equals(left, right);
        }

        public static bool operator !=(BoundingBox left, BoundingBox right)
        {
            return !Equals(left, right);
        }

        public override string ToString()
        {
            return string.Format(CultureInfo.CurrentCulture, "Minimum:{0} Maximum:{1}", Minimum, Maximum);
        }

        public override int GetHashCode()
        {
            return Minimum.GetHashCode() + Maximum.GetHashCode();
        }

        public override bool Equals(object value)
        {
            if (value == null)
                return false;

            if (value.GetType() != GetType())
                return false;

            return Equals((BoundingBox)value);
        }

        public bool Equals(BoundingBox value)
        {
            return (Minimum == value.Minimum && Maximum == value.Maximum);
        }
    }
}
