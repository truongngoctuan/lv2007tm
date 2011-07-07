/////////////////////////////////////////////////////////////
//
// ImageSelector.xaml.cs
//
// © 2008 Microsoft Corporation. All Rights Reserved.
//
// This file is licensed with terms as outlined here:
// http://go.microsoft.com/fwlink/?LinkID=111970&clcid=0x409
//
/////////////////////////////////////////////////////////////

using System;
using System.Windows;
using System.Windows.Controls;
using System.Windows.Documents;
using System.Windows.Ink;
using System.Windows.Input;
using System.Windows.Media;
using System.Windows.Media.Animation;
using System.Windows.Media.Imaging;
using System.Windows.Shapes;

namespace NavigationWithTransitions
{
    public class ImageSelectedEventArgs : EventArgs
    {
        public BitmapImage Source;
    }

    public delegate void ImageSelectedEventHandler(object sender, ImageSelectedEventArgs e);

    public partial class ImageSelector : UserControl
    {
        public event ImageSelectedEventHandler ImageSelected;

        public ImageSelector()
        {
            // Required to initialize variables
            InitializeComponent();

            imageBrushArray = new ImageBrush[7];
            imageBrushArray[0] = leftImg3Brush;
            imageBrushArray[1] = leftImg2Brush;
            imageBrushArray[2] = leftImg1Brush;
            imageBrushArray[3] = centerImgBrush;
            imageBrushArray[4] = rightImg1Brush;
            imageBrushArray[5] = rightImg2Brush;
            imageBrushArray[6] = rightImg3Brush;

            reflectionBrushArray = new ImageBrush[7];
            reflectionBrushArray[0] = leftReflection3Brush;
            reflectionBrushArray[1] = leftReflection2Brush;
            reflectionBrushArray[2] = leftReflection1Brush;
            reflectionBrushArray[3] = centerReflectionBrush;
            reflectionBrushArray[4] = rightReflection1Brush;
            reflectionBrushArray[5] = rightReflection2Brush;
            reflectionBrushArray[6] = rightReflection3Brush;

            leftImg3.MouseLeftButtonDown += new MouseButtonEventHandler(OnImgClicked);
            leftImg2.MouseLeftButtonDown += new MouseButtonEventHandler(OnImgClicked);
            leftImg1.MouseLeftButtonDown += new MouseButtonEventHandler(OnImgClicked);
            rightImg3.MouseLeftButtonDown += new MouseButtonEventHandler(OnImgClicked);
            rightImg2.MouseLeftButtonDown += new MouseButtonEventHandler(OnImgClicked);
            rightImg1.MouseLeftButtonDown += new MouseButtonEventHandler(OnImgClicked);
            centerImg.MouseLeftButtonDown += new MouseButtonEventHandler(OnImgClicked);
        }

        protected void OnImageSelected(ImageSelectedEventArgs e)
        {
            if (ImageSelected != null)
            {
                ImageSelected(this, e);
            }
        }

        public void SetImages(string[] imageUris)
        {
            imageArray = imageUris;
            //if (imageArray.Length >= 7)
            {
                imageIndex = 0;
                //System.Threading.Thread.Sleep(5000);
                UpdateImages();
            }
        }

        void OnImgClicked(object sender, MouseButtonEventArgs e)
        {
            ImageSelectedEventArgs args = new ImageSelectedEventArgs();
            args.Source = (BitmapImage)((ImageBrush)((Path)sender).Fill).ImageSource;
            OnImageSelected(args);
        }

        void onForwardFlowCompleted(object sender, EventArgs e)
        {
            firstImgBrush.ImageSource = null;
            lastImgBrush.ImageSource = null;
            firstReflectionBrush.ImageSource = null;
            lastReflectionBrush.ImageSource = null;
        }

        void onBackwardFlowCompleted(object sender, EventArgs e)
        {
            firstImgBrush.ImageSource = null;
            lastImgBrush.ImageSource = null;
            firstReflectionBrush.ImageSource = null;
            lastReflectionBrush.ImageSource = null;
        }

        void btnBack_Click(object sender, EventArgs e)
        {
            if (imageIndex != -1)
            {
                firstImgBrush.ImageSource = new BitmapImage(new Uri(imageArray[imageIndex], UriKind.RelativeOrAbsolute));
                firstReflectionBrush.ImageSource = new BitmapImage(new Uri(imageArray[imageIndex], UriKind.RelativeOrAbsolute));
                imageIndex++;
                if (imageIndex == imageArray.Length)
                {
                    imageIndex = 0;
                }
                UpdateImages();
                flowBackward.Begin();
            }
        }

        void btnForward_Click(object sender, EventArgs e)
        {
            if (imageIndex != -1)
            {
                lastImgBrush.ImageSource = new BitmapImage(new Uri(imageArray[(imageIndex + 6) % imageArray.Length], UriKind.RelativeOrAbsolute));
                lastReflectionBrush.ImageSource = new BitmapImage(new Uri(imageArray[(imageIndex + 6) % imageArray.Length], UriKind.RelativeOrAbsolute));
                imageIndex--;
                if (imageIndex < 0)
                {
                    imageIndex = imageArray.Length - 1;
                }
                UpdateImages();
                flowForward.Begin();
            }
        }

        void UpdateImages()
        {
            int brushIndex = imageIndex;
            for (int i = 0; i < 7; i++)
            {
                imageBrushArray[i].ImageSource = new BitmapImage(new Uri(imageArray[brushIndex], UriKind.RelativeOrAbsolute));
                reflectionBrushArray[i].ImageSource = new BitmapImage(new Uri(imageArray[brushIndex], UriKind.RelativeOrAbsolute));
                brushIndex++;
                if (brushIndex == imageArray.Length)
                {
                    brushIndex = 0;
                }
            }
        }

        private int imageIndex = -1;
        private ImageBrush[] imageBrushArray;
        private ImageBrush[] reflectionBrushArray;
        private string[] imageArray;
    }
}
