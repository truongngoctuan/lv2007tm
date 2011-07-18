using Babylon.Toolbox;
using System.Windows.Controls;
using Microsoft.Xna.Framework.Graphics;
using Microsoft.Xna.Framework.Silverlight;
using System;
using System.Windows;
using _3DPresentation.Models;
using Microsoft.Xna.Framework;

namespace _3DPresentation
{
    public partial class ViewScene
    {
        bool mouseLeftDown;
        float _factorRotation = 1.0f;

        public float FactorRotation
        {
            get { return _factorRotation; }
            set { _factorRotation = value;
            if (_factorRotation < 0)
            {
                _factorRotation = 1 / (-_factorRotation); 
            }
            }
        }
        float _factorTransition = 1.0f;

        public float FactorTransition
        {
            get { return _factorTransition; }
            set { _factorTransition = value;
            if (_factorTransition < 0)
            {
                _factorTransition = 1 / (-_factorTransition);
            }
            }
        }

        public void PrepareInteraction()
        {
            Container.MouseMove += new System.Windows.Input.MouseEventHandler(Container_MouseMove);
            Container.MouseWheel += new System.Windows.Input.MouseWheelEventHandler(Container_MouseWheel);
            Container.MouseEnter += new System.Windows.Input.MouseEventHandler(Container_MouseEnter);
            Container.MouseLeftButtonDown += new System.Windows.Input.MouseButtonEventHandler(Container_MouseLeftButtonDown);
            Container.MouseLeftButtonUp += new System.Windows.Input.MouseButtonEventHandler(Container_MouseLeftButtonUp);
            Container.MouseLeave += new System.Windows.Input.MouseEventHandler(Container_MouseLeave);

            Container.IsTabStop = true;
            Container.Focus();
            Container.KeyDown += new System.Windows.Input.KeyEventHandler(Container_KeyDown);
            Container.KeyUp += new System.Windows.Input.KeyEventHandler(Container_KeyUp);
        }

        void Container_KeyUp(object sender, System.Windows.Input.KeyEventArgs e)
        {
            if (e.Key == System.Windows.Input.Key.Ctrl)
            {
                CtrlKeyDown = false;
                bRotateModel = false;
            }
        }

        bool bRotateModel = false;
        bool CtrlKeyDown = false;
        void Container_KeyDown(object sender, System.Windows.Input.KeyEventArgs e)
        {
            if (e.Key == System.Windows.Input.Key.Ctrl)
            {
                CtrlKeyDown = true;
                return;
            }

            //if (e.Key == System.Windows.Input.Key.W ||
            //    e.Key == System.Windows.Input.Key.S ||
            //    e.Key == System.Windows.Input.Key.A ||
            //        e.Key == System.Windows.Input.Key.D)
            {
                Camera.ApplyInertia();
                //Microsoft.Xna.Framework.Vector3 moveDirection = Vector3.Zero;
                //Microsoft.Xna.Framework.Matrix mat = _3DPresentation.MathUtil.GetTransformationMatrix(new Vector3(0, 0, -1), Camera.Target - Camera.Position);
                //if (e.Key == System.Windows.Input.Key.W)
                //{
                //    moveDirection = MathUtil.TransformPoint(mat, Vector3.Up);
                //}
                //else if (e.Key == System.Windows.Input.Key.S)
                //{
                //    moveDirection = MathUtil.TransformPoint(mat, Vector3.Down);
                //}
                //else if (e.Key == System.Windows.Input.Key.A)
                //{
                //    moveDirection = MathUtil.TransformPoint(mat, Vector3.Left);
                //}
                //else if (e.Key == System.Windows.Input.Key.D)
                //{
                //    moveDirection = MathUtil.TransformPoint(mat, Vector3.Right);
                //}

                Microsoft.Xna.Framework.Vector3 moveDirection = Vector3.Zero;
                if (e.Key == System.Windows.Input.Key.W)
                {
                    moveDirection = Vector3.Forward;
                }
                else if (e.Key == System.Windows.Input.Key.S)
                {
                    moveDirection = Vector3.Backward;
                }
                else if (e.Key == System.Windows.Input.Key.A)
                {
                    moveDirection = Vector3.Left;
                }
                else if (e.Key == System.Windows.Input.Key.D)
                {
                    moveDirection = Vector3.Right;
                }
                else if (e.Key == System.Windows.Input.Key.Q)
                {
                    moveDirection = Vector3.Up;
                }
                else if (e.Key == System.Windows.Input.Key.E)
                {
                    moveDirection = Vector3.Down;
                }
                moveDirection *= FactorTransition / 1000.0f;

                if (KeyboardTransition != null)
                {
                    KeyboardTransitionEventArgs eArg = new KeyboardTransitionEventArgs();
                    eArg.T = moveDirection;
                    KeyboardTransition(this, eArg);
                }
            }
        }

        void Container_MouseLeave(object sender, System.Windows.Input.MouseEventArgs e)
        {
            if (MouseRotated != null)
            {
                MouseRotatedEventArgs eArg = new MouseRotatedEventArgs();
                eArg.LastRotationMatrix = Matrix.Identity;
                eArg.DeltaRotationMatrix = deltaRotationMatrix;
                eArg.IsFinished = true;
                MouseRotated(this, eArg);
            }

            mouseLeftDown = false;
            deltaRotationMatrix = Matrix.Identity;
        }

        void Container_MouseLeftButtonUp(object sender, System.Windows.Input.MouseButtonEventArgs e)
        {
            if (MouseRotated != null)
            {
                MouseRotatedEventArgs eArg = new MouseRotatedEventArgs();
                eArg.LastRotationMatrix = Matrix.Identity;
                eArg.DeltaRotationMatrix = deltaRotationMatrix;
                eArg.IsFinished = true;
                MouseRotated(this, eArg);
            }

            mouseLeftDown = false;
            deltaRotationMatrix = Matrix.Identity;


        }

        void Container_MouseLeftButtonDown(object sender, System.Windows.Input.MouseButtonEventArgs e)
        {
            Container.Focus();
            mouseLeftDown = true;
            startPosition = lastPosition = e.GetPosition(Surface);

            if (CtrlKeyDown)
            {
                bRotateModel = true;
                ChangeToRotationModelState();
            }
        }

        void Container_MouseEnter(object sender, System.Windows.Input.MouseEventArgs e)
        {
            //mouseLeftDown = false;
        }

        void Container_MouseWheel(object sender, System.Windows.Input.MouseWheelEventArgs e)
        {
            _camera.Radius -= e.Delta * _camera.Radius / 1000.0f;
            _camera.FarPlane = _camera.Radius + 500;
        }

        Point lastPosition;
        Microsoft.Xna.Framework.Vector3 lastCameraPosition;
        Microsoft.Xna.Framework.Matrix lastRotationMatrix;

        Point startPosition;
        Microsoft.Xna.Framework.Vector3 startCameraPosition;
        Microsoft.Xna.Framework.Matrix deltaRotationMatrix = Microsoft.Xna.Framework.Matrix.Identity;
        void Container_MouseMove(object sender, System.Windows.Input.MouseEventArgs e)
        {
            if (bRotateModel)
            {
                Point currentPosition = e.GetPosition(Surface);
                if (!mouseLeftDown)
                    return;
                Microsoft.Xna.Framework.Matrix lastMat = toRotationMatrix(lastPosition, currentPosition, lastCameraPosition);
                deltaRotationMatrix = toRotationMatrix(startPosition, currentPosition, startCameraPosition);
                lastPosition = currentPosition;
                if (MouseRotated != null)
                {
                    MouseRotatedEventArgs eArg = new MouseRotatedEventArgs();
                    eArg.LastRotationMatrix = lastMat;
                    eArg.DeltaRotationMatrix = deltaRotationMatrix;
                    eArg.IsFinished = false;
                    MouseRotated(this, eArg);
                }
            }
            else
            {
                Point currentPosition = e.GetPosition(Surface);
                if (!mouseLeftDown)
                    return;

                _camera.InertialAlpha += (float)(currentPosition.X - lastPosition.X) * _camera.AngularSpeed;
                _camera.InertialBeta -= (float)(currentPosition.Y - lastPosition.Y) * _camera.AngularSpeed;
                lastPosition = currentPosition;
            }
        }

        private Microsoft.Xna.Framework.Matrix toRotationMatrix(Point LastPosition, Point currentPosition,
            Vector3 LastCameraPosition)
        {
            float dX, dY;
            if (Math.Abs(currentPosition.X - LastPosition.X) < 5)
            {
                dX = 0;
            }
            else
            dX = (float)(currentPosition.X - LastPosition.X) * 3.14f / 180.0f;

            if (Math.Abs(currentPosition.Y - LastPosition.Y) < 5)
            {
                dY = 0;
            }
            else
            dY = (float)(currentPosition.Y - LastPosition.Y) * 3.14f / 180.0f;

            dX *= FactorRotation / 10;
            dY *= FactorRotation / 10;

            Microsoft.Xna.Framework.Matrix lastMat = Matrix.CreateFromYawPitchRoll(dX, dY, 0);
            return lastMat;

            //float dX, dY;
            //if (Math.Abs( currentPosition.X - LastPosition.X) < 5)
            //{
            //    dX = 0;
            //}
            //else
            //{
            //    dX = (float)(currentPosition.X - LastPosition.X) * FactorRotation;
            //}

            //if (Math.Abs( currentPosition.Y - LastPosition.Y) < 5)
            //{
            //    dY = 0;
            //}
            //else
            //{
            //    dY = (float)(currentPosition.Y - LastPosition.Y) * FactorRotation;
            //}
            //dX = -dX; dY = -dY;

            //Microsoft.Xna.Framework.Vector3 NewCamPosition = _3DPresentation.MathUtil.toNewCameraPosition(_camera, dX, dY);

            //Microsoft.Xna.Framework.Vector3 OldPos = this.Camera.Target - this.Camera.Position;
            //Microsoft.Xna.Framework.Vector3 NewPos = this.Camera.Target - NewCamPosition;

            //Microsoft.Xna.Framework.Matrix lastMat = _3DPresentation.MathUtil.GetTransformationMatrix(OldPos, NewPos);
            //return lastMat;
        }

        void ChangeToRotationModelState()
        {
            startCameraPosition = lastCameraPosition = this.Camera.Position;
            deltaRotationMatrix = lastRotationMatrix = Microsoft.Xna.Framework.Matrix.Identity;
        }

        public event MouseRotatedEventHandler MouseRotated;
        public event KeyboardTransitionEventHandler KeyboardTransition;
    }

    public class MouseRotatedEventArgs : EventArgs
    {
        public Microsoft.Xna.Framework.Matrix LastRotationMatrix;
        public Microsoft.Xna.Framework.Matrix DeltaRotationMatrix;
        public bool IsFinished;
    }

    public delegate void MouseRotatedEventHandler(object sender, MouseRotatedEventArgs e);

    public class KeyboardTransitionEventArgs : EventArgs
    {
        public Vector3 T;
    }

    public delegate void KeyboardTransitionEventHandler(object sender, KeyboardTransitionEventArgs e);
}
