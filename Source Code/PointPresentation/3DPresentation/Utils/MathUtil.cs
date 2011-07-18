using System;
using Microsoft.Xna.Framework;

namespace _3DPresentation
{
    public class MathUtil
    {
        public static double GetAngleRad(Vector3 v1, Vector3 v2)
        {
            double tichVoHuong = v1.X * v2.X + v1.Y * v2.Y + v1.Z * v2.Z;
            double tichDoLon = Math.Sqrt(v1.X * v1.X + v1.Y * v1.Y + v1.Z * v1.Z) * Math.Sqrt(v2.X * v2.X + v2.Y * v2.Y + v2.Z * v2.Z);
            double cos = tichVoHuong / tichDoLon;
            return Math.Acos(cos);
        }

        public static double GetAngle(Vector3 v1, Vector3 v2)
        {
            return GetAngleRad(v1, v2) * 180 / Math.PI;
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

        public static bool GetAngleAndAxis(Vector3 start, Vector3 dest, out double angle, out Vector3 axis)
        {
            angle = GetAngle(start, dest);
            axis = Vector3.Cross(start, dest);
            // MUST NORMALIZE THE AXIS VECTOR
            axis.Normalize();
            return true;
        }

        public static Matrix GetTransformationMatrix(Vector3 start, Vector3 dest)
        {
            double angleRad = GetAngleRad(start, dest);
            Vector3 axis = Vector3.Cross(start, dest);
            // MUST NORMALIZE THE AXIS VECTOR
            if (axis != Vector3.Zero)
            {
                axis.Normalize();
            }
            else
            {
                int a = 0;
            }

            return Matrix.CreateFromAxisAngle(axis, Convert.ToSingle(angleRad));
        }


        private static double Epsilon = 0.1f;
        private static bool CompareDouble(double a, double b)
        {
            if (b - Epsilon <= a && a <= b + Epsilon)
            {
                return true;
            }
            return false;
        }

        public static void CaculateAngleFromRotationMatrix(Matrix rotate, out double AngleX, out double AngleY, out double AngleZ)
        {
            rotate = Matrix.Transpose(rotate);
            double AngleZ1 = 0;
            double AngleX1 = 0;
            double AngleY1 = 0;
            if (!CompareDouble(rotate.M31, -1.0) && !CompareDouble(rotate.M31, 1.0))
            {
                AngleY1 = -Math.Asin(rotate.M31);
                AngleX1 = Math.Atan2(rotate.M32 / Math.Cos(AngleY1), rotate.M33 / Math.Cos(AngleY1));
                AngleZ1 = Math.Atan2(rotate.M21 / Math.Cos(AngleY1), rotate.M11 / Math.Cos(AngleY1));
                AngleX1 = (AngleX1 / 3.14 * 180.0);
                AngleY1 = (AngleY1 / 3.14 * 180.0);
                AngleZ1 = (AngleZ1 / 3.14 * 180.0);                
            }
            else
            {
                if (CompareDouble(rotate.M31, -1))
                {
                    AngleY1 = (float)(-3.14 / 2);
                    AngleX1 = 0 + Math.Atan2(rotate.M12, rotate.M13);
                }
                else
                {
                    AngleY1 = (float)(-3.14 / 2);
                    AngleX1 = 0 + Math.Atan2(-rotate.M12, -rotate.M13);
                }
            }
            AngleX = AngleX1;
            AngleY = AngleY1;
            AngleZ = AngleZ1;
        }

        public static void CaculateAngleFromRotationMatrixRad(Matrix rotate, out double AngleX, out double AngleY, out double AngleZ)
        {
            CaculateAngleFromRotationMatrix(rotate, out AngleX, out AngleY, out AngleZ);
            AngleX = AngleX * 3.14 / 180;
            AngleY = AngleX * 3.14 / 180;
            AngleZ = AngleX * 3.14 / 180;
        }

        #region OrbitCamera
        public static Microsoft.Xna.Framework.Vector3 toNewCameraPosition(Babylon.Toolbox.OrbitCamera cam, float dX, float dY)
        {
            Microsoft.Xna.Framework.Vector3 position;

            float InertialAlpha = cam.InertialAlpha;
            float InertialBeta = cam.InertialBeta;

            InertialAlpha += (float)(dX) * cam.AngularSpeed;
            InertialBeta -= (float)(dY) * cam.AngularSpeed;

            float Alpha = cam.Alpha;
            float beta = cam.Beta;

            Alpha += InertialAlpha;
            beta += InertialBeta;
            //cam.InertialAlpha *= cam.Inertia;
            //cam.InertialBeta *= cam.Inertia;

            if (beta >= Math.PI)
                beta = (float)Math.PI - cam.AngularSpeed;

            if (beta < 0)
                beta = cam.AngularSpeed;

            //compute position
            var cosa = (float)Math.Cos(Alpha);
            var sina = (float)Math.Sin(Alpha);
            var cosb = (float)Math.Cos(beta);
            var sinb = (float)Math.Sin(beta);

            position = cam.Target + new Microsoft.Xna.Framework.Vector3(cam.Radius * cosa * sinb, cam.Radius * cosb, cam.Radius * sina * sinb);

            return position;
        }
        #endregion

        public static Matrix toTransitionMatrix(Vector3 T)
        {
            Matrix mat = Matrix.Identity;
            mat.Translation = T;
            return mat;
        }
    } 
}
