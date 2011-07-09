using Babylon.Toolbox;
using System.Windows.Controls;
using Microsoft.Xna.Framework.Graphics;
using Microsoft.Xna.Framework.Silverlight;
using System;
using System.Windows;
using _3DPresentation.Models;

namespace _3DPresentation
{
    public partial class ViewScene
    {
        bool mouseLeftDown;
        Point startPosition;

        public void PrepareInteraction()
        {
            Container.MouseMove += new System.Windows.Input.MouseEventHandler(Container_MouseMove);
            Container.MouseWheel += new System.Windows.Input.MouseWheelEventHandler(Container_MouseWheel);
            Container.MouseEnter += new System.Windows.Input.MouseEventHandler(Container_MouseEnter);
            Container.MouseLeftButtonDown += new System.Windows.Input.MouseButtonEventHandler(Container_MouseLeftButtonDown);
            Container.MouseLeftButtonUp += new System.Windows.Input.MouseButtonEventHandler(Container_MouseLeftButtonUp);
        }

        void Container_MouseLeftButtonUp(object sender, System.Windows.Input.MouseButtonEventArgs e)
        {
            mouseLeftDown = false;
        }

        void Container_MouseLeftButtonDown(object sender, System.Windows.Input.MouseButtonEventArgs e)
        {
            mouseLeftDown = true;
            startPosition = e.GetPosition(Surface);
        }

        void Container_MouseEnter(object sender, System.Windows.Input.MouseEventArgs e)
        {
            mouseLeftDown = false;
        }

        void Container_MouseWheel(object sender, System.Windows.Input.MouseWheelEventArgs e)
        {
            Camera.Radius -= e.Delta * Camera.Radius / 1000.0f;
            Camera.FarPlane = Camera.Radius + 50;
        }

        void Container_MouseMove(object sender, System.Windows.Input.MouseEventArgs e)
        {
            Point currentPosition = e.GetPosition(Surface);
            if (!mouseLeftDown)
                return;

            Camera.InertialAlpha += (float)(currentPosition.X - startPosition.X) * Camera.AngularSpeed;
            Camera.InertialBeta -= (float)(currentPosition.Y - startPosition.Y) * Camera.AngularSpeed;
            startPosition = currentPosition;
        }
    }
}
