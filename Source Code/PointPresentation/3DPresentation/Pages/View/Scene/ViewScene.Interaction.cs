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
        Point startPosition;
        Microsoft.Xna.Framework.Vector3 startCameraPosition;
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

            Container.IsTabStop = true;
            Container.Focus();
            Container.KeyDown += new System.Windows.Input.KeyEventHandler(Container_KeyDown);
            Container.KeyUp += new System.Windows.Input.KeyEventHandler(Container_KeyUp);
        }

        void Container_KeyUp(object sender, System.Windows.Input.KeyEventArgs e)
        {
            CtrlKeyDown = false;
            bRotateModel = false;
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

            if (e.Key == System.Windows.Input.Key.W ||
                e.Key == System.Windows.Input.Key.S ||
                e.Key == System.Windows.Input.Key.A ||
                    e.Key == System.Windows.Input.Key.D)
            {
                Camera.ApplyInertia();
                Microsoft.Xna.Framework.Vector3 moveDirection = Vector3.Zero;
                //Microsoft.Xna.Framework.Matrix mat = Microsoft.Xna.Framework.Matrix.CreateFromYawPitchRoll(_model2.WorldMatrix. Camera.RotationY, tourControl.Camera.RotationX, tourControl.Camera.RotationZ);
                Microsoft.Xna.Framework.Matrix mat = _3DPresentation.MathUtil.GetTransformationMatrix(new Vector3(0, 0, -1), Camera.Target - Camera.Position);
                if (e.Key == System.Windows.Input.Key.W)
                {
                    moveDirection = MathUtil.TransformPoint(mat, Vector3.Up);
                }
                else if (e.Key == System.Windows.Input.Key.S)
                {
                    moveDirection = MathUtil.TransformPoint(mat, Vector3.Down);
                }
                else if (e.Key == System.Windows.Input.Key.A)
                {
                    moveDirection = MathUtil.TransformPoint(mat, Vector3.Left);
                }
                else if (e.Key == System.Windows.Input.Key.D)
                {
                    moveDirection = MathUtil.TransformPoint(mat, Vector3.Right);
                }
                moveDirection *= FactorTransition;

                if (KeyboardTransition != null)
                {
                    KeyboardTransitionEventArgs eArg = new KeyboardTransitionEventArgs();
                    eArg.T = moveDirection;
                    KeyboardTransition(this, eArg);
                }
            }
        }

        void Container_MouseLeftButtonUp(object sender, System.Windows.Input.MouseButtonEventArgs e)
        {
            mouseLeftDown = false;
        }

        void Container_MouseLeftButtonDown(object sender, System.Windows.Input.MouseButtonEventArgs e)
        {
            Container.Focus();
            mouseLeftDown = true;
            startPosition = e.GetPosition(Surface);

            if (CtrlKeyDown)
            {
                bRotateModel = true;
                ChangeToRotationModelState();
            }
        }

        void Container_MouseEnter(object sender, System.Windows.Input.MouseEventArgs e)
        {
            mouseLeftDown = false;
        }

        void Container_MouseWheel(object sender, System.Windows.Input.MouseWheelEventArgs e)
        {
            _camera.Radius -= e.Delta * _camera.Radius / 1000.0f;
            _camera.FarPlane = _camera.Radius + 500;
        }

        Microsoft.Xna.Framework.Matrix startRotationMatrix;
        void Container_MouseMove(object sender, System.Windows.Input.MouseEventArgs e)
        {
            if (bRotateModel)
            {
                Point currentPosition = e.GetPosition(Surface);
                if (!mouseLeftDown)
                    return;
                float dX, dY;
                dX = (float)(currentPosition.X - startPosition.X) * FactorRotation;
                dY = (float)(currentPosition.Y - startPosition.Y) * FactorRotation;
                dX = -dX; dY = -dY;

                Microsoft.Xna.Framework.Vector3 NewCamPosition = _3DPresentation.MathUtil.toNewCameraPosition(_camera, dX, dY);

                Microsoft.Xna.Framework.Vector3 OldPos = this.Camera.Target - startCameraPosition;
                Microsoft.Xna.Framework.Vector3 NewPos = this.Camera.Target - NewCamPosition;

                Microsoft.Xna.Framework.Matrix mat = _3DPresentation.MathUtil.GetTransformationMatrix(OldPos, NewPos);

                startPosition = currentPosition;
                if (MouseRotated != null)
                {
                    MouseRotatedEventArgs eArg = new MouseRotatedEventArgs();
                    eArg.RotationMatrix = mat;
                    MouseRotated(this, eArg);
                }
            }
            else
            {
                Point currentPosition = e.GetPosition(Surface);
                if (!mouseLeftDown)
                    return;

                _camera.InertialAlpha += (float)(currentPosition.X - startPosition.X) * _camera.AngularSpeed;
                _camera.InertialBeta -= (float)(currentPosition.Y - startPosition.Y) * _camera.AngularSpeed;
                startPosition = currentPosition;
            }
        }

        void ChangeToRotationModelState()
        {
            startCameraPosition = this.Camera.Position;
            startRotationMatrix = Microsoft.Xna.Framework.Matrix.Identity;
        }

        public event MouseRotatedEventHandler MouseRotated;
        public event KeyboardTransitionEventHandler KeyboardTransition;
    }

    public class MouseRotatedEventArgs : EventArgs
    {
        public Microsoft.Xna.Framework.Matrix RotationMatrix;
    }

    public delegate void MouseRotatedEventHandler(object sender, MouseRotatedEventArgs e);

    public class KeyboardTransitionEventArgs : EventArgs
    {
        public Vector3 T;
    }

    public delegate void KeyboardTransitionEventHandler(object sender, KeyboardTransitionEventArgs e);
}
