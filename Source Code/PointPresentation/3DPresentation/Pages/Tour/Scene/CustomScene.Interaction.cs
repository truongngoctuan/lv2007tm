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
    public partial class CustomScene : Babylon.Scene
    {
        public void PrepareInteraction()
        {
            Container.MouseLeftButtonDown += new MouseButtonEventHandler(Container_MouseLeftButtonDown);
            Container.MouseMove += new MouseEventHandler(Container_MouseMove);
        }

        void Container_MouseMove(object sender, MouseEventArgs e)
        {
            CheckPicking(e.GetPosition(Surface), new Vector2((float)Surface.ActualWidth, (float)Surface.ActualHeight));
        }

        void Container_MouseLeftButtonDown(object sender, MouseButtonEventArgs e)
        {
            if (selectedMesh != null)
            {
                // if first model == target : application crash when render

                ViewControl viewControl = new ViewControl();
                for (int i = 0; i < customSceneModels.Count; i++)
                {
                    viewControl.AddModel(customSceneModels[i]);
                }
                viewControl.SetTarget(selectedMesh);
                App.GoToPage(viewControl);
            }
        }
    }
}
