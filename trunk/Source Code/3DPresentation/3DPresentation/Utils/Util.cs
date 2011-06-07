using System;
using System.IO;
using System.Windows;
using Microsoft.Xna.Framework;


namespace _3DPresentation
{
    public class Util
    {
        public static Stream GetStream(string assembly, string path)
        {
            string uri = string.Format(@"/{0};component/{1}", assembly, path);
            return Application.GetResourceStream(new Uri(uri, UriKind.Relative)).Stream;
        }

        public static double GetAngle(Vector3 v1, Vector3 v2)
        {
            double tichVoHuong = v1.X * v2.X + v1.Y * v2.Y + v1.Z * v2.Z;
            double tichDoLon = Math.Sqrt(v1.X * v1.X + v1.Y * v1.Y + v1.Z * v1.Z) * Math.Sqrt(v2.X * v2.X + v2.Y * v2.Y + v2.Z * v2.Z);
            double cos = tichVoHuong / tichDoLon;
            return Math.Acos(cos) * 180 / Math.PI;
        }

        public static Vector3 TransformPoint(Matrix matrix, Vector3 vector)
        {
            Vector3 result = Vector3.Zero;
            result.X = vector.X * matrix.M11 + vector.Y * matrix.M21
                        + vector.Z * matrix.M31 + 1.0f * matrix.M41;
            result.Y = vector.X * matrix.M12 + vector.Y * matrix.M22
                        + vector.Z * matrix.M32 + 1.0f * matrix.M42;
            result.Z = vector.X * matrix.M13 + vector.Y * matrix.M23
                        + vector.Z * matrix.M33 + 1.0f * matrix.M43;
            return result;
        }
        public static Vector3[] TransformPoints(Matrix matrix, Vector3[] vectors)
        {
            Vector3[] results = new Vector3[vectors.Length];
            for (int i = 0; i < vectors.Length; i++)
            {
                results[i] = TransformPoint(matrix, vectors[i]);
            }
            return results;
        }
    }
}
