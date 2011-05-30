using System;
using System.Windows;
using System.Windows.Controls;
using System.Windows.Documents;
using System.Windows.Ink;
using System.Windows.Input;
using System.Windows.Media;
using System.Windows.Media.Animation;
using System.Windows.Shapes;

namespace _3DPresentation
{
	public partial class UDRMZControl : UserControl
	{
		public UDRMZControl()
		{
			// Required to initialize variables
			InitializeComponent();
		}

        public RoutedEventHandler MoveForwardClick = null;
        public RoutedEventHandler MoveBackClick = null;
        public RoutedEventHandler MoveLeftClick = null;
        public RoutedEventHandler MoveRightClick = null;

        public RoutedEventHandler RotateLeftClick = null;
        public RoutedEventHandler RotateRightClick = null;

        public RoutedEventHandler RotateUpClick = null;
        public RoutedEventHandler RotateDownClick = null;

        private void btMoveForward_Click(object sender, RoutedEventArgs e)
        {
            if (MoveForwardClick != null)
            {
                MoveForwardClick(this, e);
            }
        }

        private void btMoveBack_Click(object sender, RoutedEventArgs e)
        {
            if (MoveBackClick != null)
            {
                MoveBackClick(this, e);
            }
        }

        private void btMoveLeft_Click(object sender, RoutedEventArgs e)
        {
            if (MoveLeftClick != null)
            {
                MoveLeftClick(this, e);
            }
        }

        private void btMoveRight_Click(object sender, RoutedEventArgs e)
        {
            if (MoveRightClick != null)
            {
                MoveRightClick(this, e);
            }
        }

        private void btRotateRight_Click(object sender, RoutedEventArgs e)
        {
            if (RotateRightClick != null)
            {
                RotateRightClick(this, e);
            }
        }

        private void btRotateLeft_Click(object sender, RoutedEventArgs e)
        {
            if (RotateLeftClick != null)
            {
                RotateLeftClick(this, e);
            }
        }

        private void btMoveUp_Click(object sender, RoutedEventArgs e)
        {
            if (RotateUpClick != null)
            {
                RotateUpClick(this, e);
            }
        }

        private void btMoveDown_Click(object sender, RoutedEventArgs e)
        {
            if (RotateDownClick != null)
            {
                RotateDownClick(this, e);
            }
        }
	}
}