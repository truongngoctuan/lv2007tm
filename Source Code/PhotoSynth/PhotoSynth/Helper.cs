using System;
using System.Net;
using System.Windows;
using System.Windows.Controls;
using System.Windows.Documents;
using System.Windows.Ink;
using System.Windows.Input;
using System.Windows.Media;
using System.Windows.Media.Animation;
using System.Windows.Shapes;
using Kit3D.Windows.Media.Media3D;

namespace PhotoSynth
{
    public class Helper
    {
        public static double GetAngle(Vector3D v1, Vector3D v2)
        {
            double tichVoHuong = v1.X * v2.X + v1.Y * v2.Y + v1.Z * v2.Z;
            double tichDoLon = Math.Sqrt(v1.X * v1.X + v1.Y * v1.Y + v1.Z * v1.Z) * Math.Sqrt(v2.X * v2.X + v2.Y * v2.Y + v2.Z * v2.Z);
            double cos = tichVoHuong / tichDoLon;
            return Math.Acos(cos) * 180 / Math.PI;
        }

        public static Vector3D RotateVector3D(Vector3D vector, double rotationX, double rotationY, double rotationZ)
        {
            // Create the transform
            Transform3DGroup tg = new Transform3DGroup();
            if (rotationX != 0)
                tg.Children.Add(new RotateTransform3D(new AxisAngleRotation3D(new Vector3D(1, 0, 0), rotationX), new Point3D(0, 0, 0)));
            if (rotationY != 0)
                tg.Children.Add(new RotateTransform3D(new AxisAngleRotation3D(new Vector3D(0, 1, 0), rotationY), new Point3D(0, 0, 0)));
            if (rotationZ != 0)
                tg.Children.Add(new RotateTransform3D(new AxisAngleRotation3D(new Vector3D(0, 0, 1), rotationZ), new Point3D(0, 0, 0)));
            return tg.Value.Transform(vector);

            #region manual
            /*
            rotationX = rotationX * Math.PI / 180;
            rotationY = rotationY * Math.PI / 180;
            rotationZ = rotationZ * Math.PI / 180;
            // X Axis Rotation:
            if (rotationX != 0)
            {
                Vector3D result = new Vector3D();
                result.X = vector.X;
                result.Y = vector.Y * Math.Cos(rotationX) - vector.Z * Math.Sin(rotationX);
                result.Z = vector.Y * Math.Sin(rotationX) + vector.Z * Math.Cos(rotationX);
                vector = result;
            }

            // Y Axis Rotation:
            if (rotationY != 0)
            {
                Vector3D result = new Vector3D();
                result.X = vector.X * Math.Cos(rotationY) + vector.Z * Math.Sin(rotationY);
                result.Y = vector.Y;
                result.Z = vector.X * -Math.Sin(rotationY) + vector.Z * Math.Cos(rotationY);
                vector = result;
            }

            // Z Axis Rotation
            if (rotationZ != 0)
            {
                Vector3D result = new Vector3D();
                result.X = vector.X * Math.Cos(rotationZ) - vector.Y * Math.Sin(rotationZ);
                result.Y = vector.X * Math.Sin(rotationZ) + vector.Y * Math.Cos(rotationZ);
                result.Z = vector.Z;
                vector = result;
            }            
            
            return vector;
            */
            #endregion
        }

        public static Point3D RotatePoint3D(Point3D point, double rotationX, double rotationY, double rotationZ)
        {
            // Create the transform
            Transform3DGroup tg = new Transform3DGroup();
            if (rotationX != 0)
                tg.Children.Add(new RotateTransform3D(new AxisAngleRotation3D(new Vector3D(1, 0, 0), rotationX), new Point3D(0, 0, 0)));
            if (rotationY != 0)
                tg.Children.Add(new RotateTransform3D(new AxisAngleRotation3D(new Vector3D(0, 1, 0), rotationY), new Point3D(0, 0, 0)));
            if (rotationZ != 0)
                tg.Children.Add(new RotateTransform3D(new AxisAngleRotation3D(new Vector3D(0, 0, 1), rotationZ), new Point3D(0, 0, 0)));
            return tg.Value.Transform(point);

            #region manual
            /*
            rotationX = rotationX * Math.PI / 180;
            rotationY = rotationY * Math.PI / 180;
            rotationZ = rotationZ * Math.PI / 180;
			// X Axis Rotation:
            if (rotationX != 0)
            {
                Point3D result = new Point3D();
                result.X = point.X;
                result.Y = point.Y * Math.Cos(rotationX) - point.Z * Math.Sin(rotationX);
                result.Z = point.Y * Math.Sin(rotationX) + point.Z * Math.Cos(rotationX);                
                point = result;
            }
			
			// Y Axis Rotation:
            if (rotationY != 0)
            {
                Point3D result = new Point3D();
                result.X = point.X * Math.Cos(rotationY) + point.Z * Math.Sin(rotationY);
                result.Y = point.Y;
                result.Z = point.X * -Math.Sin(rotationY) + point.Z * Math.Cos(rotationY);
                point = result;
            }
			
			// Z Axis Rotation
            if (rotationZ != 0)
            {
                Point3D result = new Point3D();
                result.X = point.X * Math.Cos(rotationZ) - point.Y * Math.Sin(rotationZ);
                result.Y = point.X * Math.Sin(rotationZ) + point.Y * Math.Cos(rotationZ);
                result.Z = point.Z;
                point = result;
            }
            
            return point;
            */
            #endregion
        }

        public static Point3D TransformPoint3D(Point3D point, Matrix3D matrix)
        {
            // Create the transform
            MatrixTransform3D matrixTransform = new MatrixTransform3D(matrix);
            return matrixTransform.Value.Transform(point);
        }

        public static Vector3D TransformVector3D(Vector3D vector, Matrix3D matrix)
        {
            // Create the transform
            MatrixTransform3D matrixTransform = new MatrixTransform3D(matrix);
            return matrixTransform.Value.Transform(vector);
        }

        public static Point3D TransformPoint3D(Point3D point, MatrixTransform3D matrixTransform)
        {
            return matrixTransform.Value.Transform(point);
        }

        public static Vector3D TransformVector3D(Vector3D vector, MatrixTransform3D matrixTransform)
        {
            return matrixTransform.Value.Transform(vector);
        }

        public static Point3D TransformPoint3D(Point3D point, Transform3DGroup transformGroup)
        {
            return transformGroup.Value.Transform(point);
        }

        public static Vector3D TransformVector3D(Vector3D vector, Transform3DGroup transformGroup)
        {
            return transformGroup.Value.Transform(vector);
        }
    }
}
