using System;
using Microsoft.Xna.Framework;

namespace Babylon
{
    public class InputManager
    {
        Vector2 cameraRotation;
        Vector3 cameraDirection;
        Vector2? originalPosition;
        readonly Scene scene;
        bool needCollision;

        internal InputManager(Scene scene)
        {
            this.scene = scene;
        }

        float GetLinearCameraSpeed(double deltaTime)
        {
            return (scene.ActiveCamera.Speed * scene.ActiveCamera.SpeedFactor) * (float)((deltaTime / (scene.Engine.FPS * 100.0)));
        }

        public void HandleMouseDown(Vector2 position)
        {
            originalPosition = position;
        }

        public void CheckKeyboard(MoveDirection moveDirection, double deltaTime)
        {
            float speed = GetLinearCameraSpeed(deltaTime);
            Vector3 direction = Vector3.Zero;

            switch (moveDirection)
            {
                case MoveDirection.Left:
                    direction = new Vector3(-speed, 0, 0);
                    break;
                case MoveDirection.Right:
                    direction = new Vector3(speed, 0, 0);
                    break;
                case MoveDirection.Forward:
                    direction = new Vector3(0, 0, speed);
                    break;
                case MoveDirection.Backward:
                    direction = new Vector3(0, 0, -speed);
                    break;
            }

            cameraDirection += GetDirectionInCameraWorld(direction, false);
        }

        public void HandleMouseUp()
        {
            originalPosition = null;
        }

        public void HandleMouseMove(Vector2 position)
        {
            if (scene.ActiveCamera == null)
                return;

            if (!originalPosition.HasValue)
                originalPosition = position;

            Vector2 diff = (originalPosition.Value - position);

            if (diff == Vector2.Zero)
                return;

            if (diff.X == 0)
            {
                int side = 0;

                if (position.X == 0)
                {
                    side = -1;
                }
                else if (position.X == scene.Engine.RenderWidth - 1)
                {
                    side = 1;
                }

                diff.X -= 10 * side;
            }

            diff *= 0.0004f;

            cameraRotation -= new Vector2(diff.Y, diff.X);

            originalPosition = position;
        }

        Vector3 GetDirectionInCameraWorld(Vector3 refVector, bool forceOnlyYAxis)
        {
            Camera camera = scene.ActiveCamera;
            Matrix matrix;

            if (camera == null)
                return Vector3.Zero;

            if (forceOnlyYAxis)
                matrix = MatrixLeftHanded.CreateRotationY(camera.Rotation.Y) * Matrix.CreateRotationZ(camera.Rotation.Z);
            else
                matrix = MatrixLeftHanded.CreateFromYawPitchRoll(camera.Rotation.Y, camera.Rotation.X, 0) * Matrix.CreateRotationZ(camera.Rotation.Z);

            return Vector3.Transform(refVector, matrix);
        }

        internal void MoveCamera()
        {
            if (scene == null || scene.ActiveCamera == null)
                return;

            // Rotate
            bool needToRotate = Math.Abs(cameraRotation.X) > 0 || Math.Abs(cameraRotation.Y) > 0;

            if (needToRotate)
            {
                scene.ActiveCamera.RotationX += cameraRotation.X;
                scene.ActiveCamera.RotationY += cameraRotation.Y;

                const float limit = (float)(Math.PI / 2) * 0.95f;
                if (scene.ActiveCamera.RotationX > limit)
                    scene.ActiveCamera.RotationX = limit;
                if (scene.ActiveCamera.RotationX < -limit)
                    scene.ActiveCamera.RotationX = -limit;
            }
            // Move
            bool needToMove = Math.Abs(cameraDirection.X) > 0 || Math.Abs(cameraDirection.Y) > 0 || Math.Abs(cameraDirection.Z) > 0;

            if (scene.CheckCollisions && scene.ActiveCamera.CheckCollisions)
            {
                if (needToMove || needCollision)
                {
                    needCollision = false;
                    scene.ActiveCamera.EllipsoidOffset.Y = -scene.ActiveCamera.Ellipsoid.Y;

                    scene.ActiveCamera.Move(cameraDirection);

                    if (!scene.ActiveCamera.IsFlying)
                    {
                        Vector3 oldCameraPosition = scene.ActiveCamera.Position;

                        scene.ActiveCamera.Move(scene.Gravity);

                        if (oldCameraPosition != scene.ActiveCamera.Position)
                            needCollision = true;
                    }
                }
            }
            else
            {
                scene.ActiveCamera.Position += cameraDirection;
            }

            float inertia = scene.ActiveCamera.Inertia;

            // Inertia
            if (needToMove)
            {
                if (cameraDirection.X != 0)
                    cameraDirection.X *= inertia;

                if (cameraDirection.Y != 0)
                    cameraDirection.Y *= inertia;

                if (cameraDirection.Z != 0)
                    cameraDirection.Z *= inertia;
            }

            if (needToRotate)
            {
                if (cameraRotation.X != 0)
                    cameraRotation.X *= inertia;

                if (cameraRotation.Y != 0)
                    cameraRotation.Y *= inertia;
            }
        }
    }
}
