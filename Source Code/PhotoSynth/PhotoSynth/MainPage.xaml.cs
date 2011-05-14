using System;
using System.Windows;
using System.Windows.Controls;
using System.Windows.Documents;
using System.Windows.Ink;
using System.Windows.Input;
using System.Windows.Media;
using System.Windows.Media.Animation;
using System.Windows.Shapes;

namespace PhotoSynth
{
	public partial class MainPage : UserControl
	{
		public MainPage()
		{
			// Required to initialize variables
			InitializeComponent();
			ClickToStart.MouseLeftButtonDown += new System.Windows.Input.MouseButtonEventHandler(ClickToStart_MouseLeftButtonDown);
		}

		private void ClickToStart_MouseLeftButtonDown(object sender, System.Windows.Input.MouseButtonEventArgs e)
		{
			// TODO: Add event handler implementation here.
			RootCanvas.Children.Remove(ClickToStart);
			LayoutRoot.Opacity = 1.0;
			Start();
		}
		
		private void Start()
		{
			ImageSpace3D.Start();
		}
	}
}