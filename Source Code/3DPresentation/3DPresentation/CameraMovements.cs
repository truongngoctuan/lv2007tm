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
using Microsoft.Xna.Framework;

namespace _3DPresentation
{
    public class CameraMovements
    {//http://www.xnawiki.com/index.php?title=Easy_Camera_Movement_Class
        public enum MOVE { FORWARD, BACK, LEFT, RIGHT}
        static public Vector3 CameraResult; //This Vector3 holds the general camera movements
        static public Vector3 LookAtResult; //This Vector3 holds the movements of the LookAt and only them.

        static public void Move(Vector3 CameraPosition, Vector3 LookAt, float Speed, MOVE Type)
        {
            //Create all needed values:
            #region Create Values

            //The direction from the Camera to the LookAt:
            Vector3 Direction = LookAt - CameraPosition;

            Direction.Normalize();

            //This Vector3 defines the relative X-axis of the view (Forward).
            Vector3 RelativeX = Direction;

            //AlphaY holds the rotation of RelativeX around the absolute Y-axis, starting at the absolute X-axis.
            float AlphaY = 0.0f;

            if (RelativeX.Z >= 0)
            {
                AlphaY = (float)Math.Atan2(RelativeX.Z, RelativeX.X);
            }
            else if (RelativeX.Z < 0)
            {
                AlphaY = (float)Math.Atan2(RelativeX.Z, RelativeX.X) + (2 * (float)Math.PI);
            }

            //AlphaZ holds the rotation of RelativeX around the RelativeZ axis (Right).
            //RelativeZ will be defined later, based on RelativeX.
            float AlphaZ = -(float)Math.Atan(RelativeX.Y /
            (float)Math.Sqrt(Math.Pow(RelativeX.X, 2f) + Math.Pow(RelativeX.Z, 2f)));
            //The RelativeZ axis holds the driection Right. It will be used for movements.
            Vector3 RelativeZ;
            RelativeZ.X = RelativeX.Z;
            RelativeZ.Y = 0.0f;
            RelativeZ.Z = -RelativeX.X;

            RelativeZ.Normalize();

            //The RelativeY axis holds the direction Up. Again it will be used for movements.
            Vector3 RelativeY = new Vector3(0, 1, 0);

            RelativeY.X = -RelativeX.Y;
            RelativeY.Y = (float)Math.Sqrt(Math.Pow(RelativeX.X, 2f) + Math.Pow(RelativeX.Z, 2f));

            RelativeY = Vector3.Transform(RelativeY, Microsoft.Xna.Framework.Matrix.CreateRotationY(-AlphaY));

            RelativeY.Normalize();
            #endregion

            //Velocity holds the movement of the Camera and the LookAt in the absolute space.
            Vector3 Velocity = Vector3.Zero;
            if (Type == MOVE.FORWARD)
            {
                Velocity += RelativeX * Speed;
            }
            if (Type == MOVE.BACK)
            {
                Velocity -= RelativeX * Speed;
            }
            if (Type == MOVE.LEFT)
            {
                Velocity += RelativeZ * Speed;
            }
            if (Type == MOVE.RIGHT)
            {
                Velocity -= RelativeZ * Speed;
            }

            CameraResult = CameraPosition + Velocity;
            LookAtResult = LookAt + Velocity;
        }

        public enum ROTATE { LEFT, RIGHT}
        static public void Rotate(Vector2 mousemove, Vector3 CameraPosition, Vector3 LookAt)
        {
            Vector3 Direction = LookAt - CameraPosition;

            Direction.Normalize();

            //This Vector3 defines the relative X-axis of the view (Forward).
            Vector3 RelativeX = Direction;

            //AlphaY holds the rotation of RelativeX around the absolute Y-axis, starting at the absolute X-axis.
            float AlphaY = 0.0f;

            if (RelativeX.Z >= 0)
            {
                AlphaY = (float)Math.Atan2(RelativeX.Z, RelativeX.X);
            }
            else if (RelativeX.Z < 0)
            {
                AlphaY = (float)Math.Atan2(RelativeX.Z, RelativeX.X) + (2 * (float)Math.PI);
            }

            //AlphaZ holds the rotation of RelativeX around the RelativeZ axis (Right).
            //RelativeZ will be defined later, based on RelativeX.
            float AlphaZ = -(float)Math.Atan(RelativeX.Y /
            (float)Math.Sqrt(Math.Pow(RelativeX.X, 2f) + Math.Pow(RelativeX.Z, 2f)));
            //The RelativeZ axis holds the driection Right. It will be used for movements.
            Vector3 RelativeZ;
            RelativeZ.X = RelativeX.Z;
            RelativeZ.Y = 0.0f;
            RelativeZ.Z = -RelativeX.X;

            RelativeZ.Normalize();

            // This float holds the Angle the camera has moved around the Z.axis since last frame.
            float AngleAddZ = 0;

            // This float holds the Angle the camera has moved around the Y.axis since last frame.
            float AngleAddY = 0;

            //This Vektor holds the relative position of the LookAt based on the CameraPosition,
            //It will be importent to calculate the new LookAt position.
            Vector3 Before = CameraPosition - LookAt;

            //After is the vector holding the new relative position of the LookAt.
            Vector3 After = Vector3.Zero;

            //This Vector will hold the movement of the LookAt that, when applied, will cause the LookAt to
            //rotate around the camera.
            Vector3 Rotation;

            //int MonitorWidth = 1440;
            //int MonitorHeight = 900;

            //mousemove.X = mouse.Y - (MonitorHeight / 2);
            //mousemove.Y = mouse.X - (MonitorWidth / 2);

            AngleAddZ = (float)MathHelper.ToRadians(mousemove.X / 3);
            AngleAddY = -(float)MathHelper.ToRadians(mousemove.Y / 3);

            //Now applay the mousemovements:

            Microsoft.Xna.Framework.Matrix RotationMatrix =
                  Microsoft.Xna.Framework.Matrix.CreateFromAxisAngle(RelativeZ, AngleAddZ) *
                  Microsoft.Xna.Framework.Matrix.CreateRotationY(AngleAddY);

            After = Vector3.Transform(Before, RotationMatrix);

            Rotation = Before - After;

            LookAtResult = LookAt + Rotation;
        }
    }
}
