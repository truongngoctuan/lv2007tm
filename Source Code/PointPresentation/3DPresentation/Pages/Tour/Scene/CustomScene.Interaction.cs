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
using _3DPresentation.Models;

namespace _3DPresentation
{
    public partial class CustomScene : Babylon.Scene
    {
        public event EventHandler SelectingModel;
        bool mouseLeftDown;
        Point startPosition;

        public void PrepareInteraction()
        {
            Container.MouseLeftButtonDown += new MouseButtonEventHandler(Container_MouseLeftButtonDown);
            Container.MouseLeftButtonUp += new MouseButtonEventHandler(Container_MouseLeftButtonUp);
            Container.MouseMove += new MouseEventHandler(Container_MouseMove);
        }

        void Container_MouseMove(object sender, MouseEventArgs e)
        {
            selectedMesh = CheckPicking(e.GetPosition(Surface), new Vector2((float)Surface.ActualWidth, (float)Surface.ActualHeight));
        }
        
        void Container_MouseLeftButtonDown(object sender, MouseButtonEventArgs e)
        {
            mouseLeftDown = true;
            startPosition = e.GetPosition(Surface);
        }

        void Container_MouseLeftButtonUp(object sender, MouseButtonEventArgs e)
        {
            mouseLeftDown = false;
            Point upPosition = e.GetPosition(Surface);
            if (Math.Abs(upPosition.X - startPosition.X) < 5 && Math.Abs(upPosition.Y - startPosition.Y) < 5)
            {
                OnMouseClick();
            }
        }

        private void OnMouseClick()
        {
            if (selectedMesh != null)
            {
                if (SelectingModel != null)
                    SelectingModel(this, EventArgs.Empty);                
            }
        }
    }
}
