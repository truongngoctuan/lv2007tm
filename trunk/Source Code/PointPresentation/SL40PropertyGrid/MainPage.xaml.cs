using System;
using System.Collections.Generic;
using System.Linq;
using System.Net;
using System.Windows;
using System.Windows.Controls;
using System.Windows.Documents;
using System.Windows.Input;
using System.Windows.Media;
using System.Windows.Media.Animation;
using System.Windows.Shapes;

namespace SL40PropertyGrid
{
	public partial class MainPage : UserControl
	{
		Person person;

		public MainPage()
		{
			InitializeComponent();
			this.Loaded += new RoutedEventHandler(Page_Loaded);
		}

		void Page_Loaded(object sender, RoutedEventArgs e)
		{
			person = new Person
			{
				String = "Bill Gates",
				Datetime = new DateTime(1985, 8, 9),
				Int = -42,
				Short = 21,
				Long = -2878987,
				Uint = 324,
				Ushort = 21,
				Ulong = 21422,
				Car = new Car()
			};
			this.propertyGrid.SelectedObject = person;
		}

		private void test_Click(object sender, RoutedEventArgs e)
		{

            
            if (this.propertyGrid.SelectedObject == this.person.Car)
            {
                this.propertyGrid.SelectedObject = null;
                person.Car.Position = new Microsoft.Xna.Framework.Vector3(4, 4 ,4);;
            }
            else
            {
                this.propertyGrid.SelectedObject = this.person.Car;
                //person.Car.Brand = "ooops...";
            }
             
        }
	}
}
