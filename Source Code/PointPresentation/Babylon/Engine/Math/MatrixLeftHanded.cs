using System;
using Microsoft.Xna.Framework;

namespace Babylon
{
    //nhminh
    //internal static class MatrixLeftHanded
    public static class MatrixLeftHanded
    {
        public static Matrix CreateTranslation(Vector3 translation)
        {
            Matrix result = Matrix.Identity;

            result.M41 = translation.X;
            result.M42 = translation.Y;
            result.M43 = translation.Z;

            return result;
        }

        public static Matrix CreateFromYawPitchRoll(float yaw, float pitch, float roll)
        {
            return CreateRotationZ(roll) * CreateRotationX(pitch) * CreateRotationY(yaw);
        }

        public static Matrix Invert(Matrix matrix)
        {
            Matrix result = new Matrix();

            float L1 = matrix.M11;
            float L2 = matrix.M12;
            float L3 = matrix.M13;
            float L4 = matrix.M14;
            float L5 = matrix.M21;
            float L6 = matrix.M22;
            float L7 = matrix.M23;
            float L8 = matrix.M24;
            float L9 = matrix.M31;
            float L10 = matrix.M32;
            float L11 = matrix.M33;
            float L12 = matrix.M34;
            float L13 = matrix.M41;
            float L14 = matrix.M42;
            float L15 = matrix.M43;
            float L16 = matrix.M44;
            float L17 = (L11 * L16) - (L12 * L15);
            float L18 = (L10 * L16) - (L12 * L14);
            float L19 = (L10 * L15) - (L11 * L14);
            float L20 = (L9 * L16) - (L12 * L13);
            float L21 = (L9 * L15) - (L11 * L13);
            float L22 = (L9 * L14) - (L10 * L13);
            float L23 = ((L6 * L17) - (L7 * L18)) + (L8 * L19);
            float L24 = -(((L5 * L17) - (L7 * L20)) + (L8 * L21));
            float L25 = ((L5 * L18) - (L6 * L20)) + (L8 * L22);
            float L26 = -(((L5 * L19) - (L6 * L21)) + (L7 * L22));
            float L27 = 1f / ((((L1 * L23) + (L2 * L24)) + (L3 * L25)) + (L4 * L26));
            float L28 = (L7 * L16) - (L8 * L15);
            float L29 = (L6 * L16) - (L8 * L14);
            float L30 = (L6 * L15) - (L7 * L14);
            float L31 = (L5 * L16) - (L8 * L13);
            float L32 = (L5 * L15) - (L7 * L13);
            float L33 = (L5 * L14) - (L6 * L13);
            float L34 = (L7 * L12) - (L8 * L11);
            float L35 = (L6 * L12) - (L8 * L10);
            float L36 = (L6 * L11) - (L7 * L10);
            float L37 = (L5 * L12) - (L8 * L9);
            float L38 = (L5 * L11) - (L7 * L9);
            float L39 = (L5 * L10) - (L6 * L9);

            result.M11 = L23 * L27;
            result.M21 = L24 * L27;
            result.M31 = L25 * L27;
            result.M41 = L26 * L27;
            result.M12 = -(((L2 * L17) - (L3 * L18)) + (L4 * L19)) * L27;
            result.M22 = (((L1 * L17) - (L3 * L20)) + (L4 * L21)) * L27;
            result.M32 = -(((L1 * L18) - (L2 * L20)) + (L4 * L22)) * L27;
            result.M42 = (((L1 * L19) - (L2 * L21)) + (L3 * L22)) * L27;
            result.M13 = (((L2 * L28) - (L3 * L29)) + (L4 * L30)) * L27;
            result.M23 = -(((L1 * L28) - (L3 * L31)) + (L4 * L32)) * L27;
            result.M33 = (((L1 * L29) - (L2 * L31)) + (L4 * L33)) * L27;
            result.M43 = -(((L1 * L30) - (L2 * L32)) + (L3 * L33)) * L27;
            result.M14 = -(((L2 * L34) - (L3 * L35)) + (L4 * L36)) * L27;
            result.M24 = (((L1 * L34) - (L3 * L37)) + (L4 * L38)) * L27;
            result.M34 = -(((L1 * L35) - (L2 * L37)) + (L4 * L39)) * L27;
            result.M44 = (((L1 * L36) - (L2 * L38)) + (L3 * L39)) * L27;

            return result;
        }

        public static Matrix CreateRotationX(float angle)
        {
            Matrix result = new Matrix();
            float s = (float)Math.Sin(angle);
            float c = (float)Math.Cos(angle);

            result.M11 = 1.0f;
            result.M44 = 1.0f;

            result.M22 = c;
            result.M33 = c;
            result.M32 = -s;
            result.M23 = s;

            return result;
        }

        public static Matrix CreateRotationY(float angle)
        {
            Matrix result = new Matrix();
            float s = (float)Math.Sin(angle);
            float c = (float)Math.Cos(angle);

            result.M22 = 1.0f;
            result.M44 = 1.0f;

            result.M11 = c;
            result.M13 = -s;
            result.M31 = s;
            result.M33 = c;

            return result;
        }

        public static Matrix CreateRotationZ(float angle)
        {
            Matrix result = new Matrix();
            float s = (float)Math.Sin(angle);
            float c = (float)Math.Cos(angle);

            result.M33 = 1.0f;
            result.M44 = 1.0f;

            result.M11 = c;
            result.M12 = s;
            result.M21 = -s;
            result.M22 = c;

            return result;
        }

        public static Matrix CreateLookAt(Vector3 eye, Vector3 target, Vector3 up)
        {
            // Z axis
            Vector3 zAxis = target - eye;
            zAxis.Normalize();

            // X axis
            Vector3 xAxis = Vector3.Cross(up, zAxis);
            xAxis.Normalize();

            // Y axis
            Vector3 yAxis = Vector3.Cross(zAxis, xAxis);
            yAxis.Normalize();

            // Eye angles
            float ex = -Vector3.Dot(xAxis, eye);
            float ey = -Vector3.Dot(yAxis, eye);
            float ez = -Vector3.Dot(zAxis, eye);

            return new Matrix(xAxis.X, yAxis.X, zAxis.X, 0,
                                xAxis.Y, yAxis.Y, zAxis.Y, 0,
                                xAxis.Z, yAxis.Z, zAxis.Z, 0,
                                ex, ey, ez, 1);
        }

        public static Matrix CreatePerspectiveFieldOfView(float fov, float aspect, float znear, float zfar)
        {
            Matrix matrix = new Matrix();
            if ((fov <= 0f) || (fov >= (float)Math.PI))
            {
                throw new ArgumentOutOfRangeException("fov");
            }
            if (znear >= zfar)
            {
                throw new ArgumentOutOfRangeException("znear");
            }
            float tan = 1f / ((float)Math.Tan(fov * 0.5f));
            matrix.M11 = tan / aspect;
            matrix.M12 = matrix.M13 = matrix.M14 = 0f;
            matrix.M22 = tan;
            matrix.M21 = matrix.M23 = matrix.M24 = 0f;
            matrix.M31 = matrix.M32 = 0f;
            matrix.M33 = -zfar / (znear - zfar);
            matrix.M34 = 1f;
            matrix.M41 = matrix.M42 = matrix.M44 = 0f;
            matrix.M43 = (znear * zfar) / (znear - zfar);
            return matrix;
        }

        public static Matrix CreateScale(float determinant)
        {
            return CreateScale(new Vector3(determinant));
        }

        public static Matrix CreateScale(Vector3 scale)
        {
            Matrix result = new Matrix {M11 = scale.X, M22 = scale.Y, M33 = scale.Z, M44 = 1.0f};

            return result;
        }

        public static Matrix CreateScale(float x, float y, float z)
        {
            Matrix result = new Matrix {M11 = x, M22 = y, M33 = z, M44 = 1.0f};

            return result;
        }
    }
}
