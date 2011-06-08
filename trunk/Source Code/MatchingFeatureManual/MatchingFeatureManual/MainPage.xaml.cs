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
using System.Windows.Media.Imaging;
using System.IO;

namespace MatchingFeatureManual
{
    public partial class MainPage : UserControl
    {
        CanvasFeaturePair customCanvas;
        public MainPage()
        {
            InitializeComponent();

            customCanvas = new CanvasFeaturePair();
            myCanvas.Children.Add(customCanvas);
        }

        private void Button_Click(object sender, RoutedEventArgs e)
        {
            customCanvas.DeleteSelectedFeature();
        }

        private void Button_Click_1(object sender, RoutedEventArgs e)
        {
            customCanvas.AddNewPair();
        }

        private void Button_Click_2(object sender, RoutedEventArgs e)
        {
            customCanvas.Clear();
            customCanvas.ReadFromFile("d:\\pairs.txt");
        }

        private void Button_Click_3(object sender, RoutedEventArgs e)
        {
            customCanvas.SaveToFile("d:\\pairs.txt");
        }

    }
}
