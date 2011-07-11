﻿using System;
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

namespace _3DPresentation.Views.Editor
{
    public partial class ComboboxCoverFlow : UserControl
    {
        public event ImageSelectedEventHandler ImageSelected;

        public ComboboxCoverFlow()
        {
            // Required to initialize variables
            InitializeComponent();
            BitmapImage asd = new BitmapImage();
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

            leftImg3.MouseLeftButtonDown += new MouseButtonEventHandler(OnImgClicked1);
            leftImg2.MouseLeftButtonDown += new MouseButtonEventHandler(OnImgClicked2);
            leftImg1.MouseLeftButtonDown += new MouseButtonEventHandler(OnImgClicked3);
            rightImg3.MouseLeftButtonDown += new MouseButtonEventHandler(OnImgClicked7);
            rightImg2.MouseLeftButtonDown += new MouseButtonEventHandler(OnImgClicked6);
            rightImg1.MouseLeftButtonDown += new MouseButtonEventHandler(OnImgClicked5);
            centerImg.MouseLeftButtonDown += new MouseButtonEventHandler(OnImgClicked4);

            this.SetImages(new PathUri[] {});
        }

        protected void OnImageSelected(ImageSelectedEventArgs e)
        {
            if (ImageSelected != null)
            {
                ImageSelected(this, e);
            }
        }

        int brushIndex = -1;
        int realLength = -1;

        public void SetImages(PathUri[] imageUris)
        {
            ImageArray = imageUris;
            if (ImageArray.Length >= 7)
            {
                imageIndex = ImageArray.Length - 1;
                brushIndex = (imageIndex + ImageArray.Length - 3) % ImageArray.Length;
                realLength = ImageArray.Length;
                //System.Threading.Thread.Sleep(5000);
                UpdateImages();
            }
            else
            {
                realLength = ImageArray.Length;
                List<PathUri> arr = new List<PathUri>();
                arr.AddRange(ImageArray);
                imageIndex = ImageArray.Length - 1;

                for (int i = 0; i < 7 - ImageArray.Length; i++)
                {
                    //arr.Add(UriToBitmapImage("Images/blank.jpg"));
                    arr.Add(new PathUri("Views/Editor/Images/blank.jpg", false));
                }

                ImageArray = arr.ToArray();
                brushIndex = (imageIndex + ImageArray.Length - 3) % ImageArray.Length;//imageArray.Length - 1;
                
                UpdateImages();
            }
        }

        public void AddImage(object obj, PathUri strFileName)
        {
            try
            {
                Items.Add(obj);
                if (realLength < 7)
                {
                    List<PathUri> arr = new List<PathUri>();
                    for (int i = 0; i < realLength; i++)
                    {
                        arr.Add(ImageArray[i]);
                    }
                    arr.Add(strFileName);
                    realLength++;

                    for (int i = 0; i < 7 - realLength; i++)
                    {
                        arr.Add(new PathUri("Views/Editor/Images/blank.jpg", false));
                    }
                    ImageArray = arr.ToArray();

                    if (imageIndex + 1 == realLength - 1)
                    {//have effect back coverflow
                        firstImgBrush.ImageSource = ImageArray[brushIndex].toBitmapImage();
                        firstReflectionBrush.ImageSource = ImageArray[brushIndex].toBitmapImage();

                        imageIndex = (++imageIndex + ImageArray.Length) % ImageArray.Length;
                        brushIndex = (imageIndex + ImageArray.Length - 3) % ImageArray.Length;

                        UpdateImages();
                        flowBackward.Begin();
                    }
                    else
                    {
                        brushIndex = (imageIndex + ImageArray.Length - 3) % ImageArray.Length;

                        UpdateImages();
                    }
                }
                else
                {
                    List<PathUri> arr = new List<PathUri>();
                    arr.AddRange(ImageArray);
                    arr.Add(strFileName);
                    realLength++;
                    ImageArray = arr.ToArray();

                    if (imageIndex + 1 == ImageArray.Length - 1)
                    {//have effect back coverflow
                        firstImgBrush.ImageSource = ImageArray[brushIndex].toBitmapImage();
                        firstReflectionBrush.ImageSource = ImageArray[brushIndex].toBitmapImage();

                        imageIndex = (++imageIndex + ImageArray.Length) % ImageArray.Length;
                        brushIndex = (imageIndex + ImageArray.Length - 3) % ImageArray.Length;

                        UpdateImages();
                        flowBackward.Begin();
                    }
                    else
                    {
                        brushIndex = (imageIndex + ImageArray.Length - 3) % ImageArray.Length;
                        UpdateImages();
                    }
                }
            }
            catch (Exception ex)
            {
                MessageBox.Show(ex.Message);
            }
        }

        public void DeleteImage(int iIndex)
        {
            try
            {
                if (realLength < 7)
                {
                }
                else
                {
                    List<PathUri> arr = new List<PathUri>();
                    arr.AddRange(ImageArray);
                    arr.RemoveAt(iIndex);

                    ImageArray = arr.ToArray();

                    if (imageIndex + 1 == ImageArray.Length - 1)
                    {//have effect back coverflow
                        firstImgBrush.ImageSource = ImageArray[brushIndex].toBitmapImage();
                        firstReflectionBrush.ImageSource = ImageArray[brushIndex].toBitmapImage();

                        imageIndex = (++imageIndex + ImageArray.Length) % ImageArray.Length;
                        brushIndex = (imageIndex + ImageArray.Length - 3) % ImageArray.Length;

                        UpdateImages();
                        flowBackward.Begin();
                    }
                    else
                    {
                        brushIndex = (imageIndex + ImageArray.Length - 3) % ImageArray.Length;
                        UpdateImages();
                    }
                }
            }
            catch (Exception ex)
            {
                MessageBox.Show(ex.Message);
            }
        }

        #region Clicked

        void OnImgClicked1(object sender, MouseButtonEventArgs e)
        {
            SelectedIndex = (imageIndex + ImageArray.Length - 3) % ImageArray.Length;
            OnImgClicked(sender, e);
        }
        void OnImgClicked2(object sender, MouseButtonEventArgs e)
        {
            SelectedIndex = (imageIndex + ImageArray.Length - 2) % ImageArray.Length;
            OnImgClicked(sender, e);
        }
        void OnImgClicked3(object sender, MouseButtonEventArgs e)
        {
            SelectedIndex = (imageIndex + ImageArray.Length - 1) % ImageArray.Length;
            OnImgClicked(sender, e);
        }

        void OnImgClicked4(object sender, MouseButtonEventArgs e)
        {
            SelectedIndex = imageIndex;
            OnImgClicked(sender, e);
        }

        void OnImgClicked5(object sender, MouseButtonEventArgs e)
        {
            SelectedIndex = (imageIndex + ImageArray.Length + 1) % ImageArray.Length;
            OnImgClicked(sender, e);
        }
        void OnImgClicked6(object sender, MouseButtonEventArgs e)
        {
            SelectedIndex = (imageIndex + ImageArray.Length + 2) % ImageArray.Length;
            OnImgClicked(sender, e);
        }
        void OnImgClicked7(object sender, MouseButtonEventArgs e)
        {
            SelectedIndex = (imageIndex + ImageArray.Length + 3) % ImageArray.Length;
            OnImgClicked(sender, e);
        }

        void OnImgClicked(object sender, MouseButtonEventArgs e)
        {
            ImageSelectedEventArgs args = new ImageSelectedEventArgs();
            args.Source = (BitmapImage)((ImageBrush)((System.Windows.Shapes.Path)sender).Fill).ImageSource;
            OnImageSelected(args);
            //ClickedPositionParent = e.GetPosition(_parent);

            if (SelectionChanged != null)
            {
                SelectionChanged(this, new EventArgs());
            }
            
        }

        #endregion

        void onForwardFlowCompleted(object sender, EventArgs e)
        {
            try
            {
                firstImgBrush.ImageSource = null;
                lastImgBrush.ImageSource = null;
                firstReflectionBrush.ImageSource = null;
                lastReflectionBrush.ImageSource = null;
            }
            catch (Exception ex)
            {
                MessageBox.Show(ex.Message);
            }
        }

        void onBackwardFlowCompleted(object sender, EventArgs e)
        {
            try{
            firstImgBrush.ImageSource = null;
            lastImgBrush.ImageSource = null;
            firstReflectionBrush.ImageSource = null;
            lastReflectionBrush.ImageSource = null;
            }
            catch (Exception ex)
            {
                MessageBox.Show(ex.Message);
            }
        }

        void btnBack_Click(object sender, EventArgs e)
        {
            if (imageIndex != -1)
            {
                if (imageIndex + 1 == realLength &&realLength < 7) return;
                firstImgBrush.ImageSource = ImageArray[brushIndex].toBitmapImage();
                firstReflectionBrush.ImageSource = ImageArray[brushIndex].toBitmapImage();
                imageIndex++;
                if (imageIndex == ImageArray.Length)
                {
                    imageIndex = 0;
                }

                brushIndex++;
                if (brushIndex == ImageArray.Length)
                {
                    brushIndex = 0;
                }

                UpdateImages();
                flowBackward.Begin();
            }
        }

        void btnForward_Click(object sender, EventArgs e)
        {
            if (imageIndex != -1)
            {
                if (imageIndex == 0 && realLength < 7) return;
                lastImgBrush.ImageSource = ImageArray[(brushIndex + 6) % ImageArray.Length].toBitmapImage();
                lastReflectionBrush.ImageSource = ImageArray[(brushIndex + 6) % ImageArray.Length].toBitmapImage();

                imageIndex--;
                if (imageIndex < 0)
                {
                    imageIndex = ImageArray.Length - 1;
                }

                brushIndex--;
                if (brushIndex < 0)
                {
                    brushIndex = ImageArray.Length - 1;
                }

                UpdateImages();
                flowForward.Begin();
            }
        }

        void UpdateImages()
        {
            //int brushIndex = imageIndex;
            int CurrentBrushIndex = brushIndex;
            for (int i = 0; i < 7; i++)
            {
                imageBrushArray[i].ImageSource = ImageArray[CurrentBrushIndex].toBitmapImage();
                reflectionBrushArray[i].ImageSource = ImageArray[CurrentBrushIndex].toBitmapImage();
                CurrentBrushIndex++;
                if (CurrentBrushIndex == ImageArray.Length)
                {
                    CurrentBrushIndex = 0;
                }
            }

            SetCurrentInfoFrame();
        }

        void SetCurrentInfoFrame()
        {
            tbCurrentFrameIndex.Text = imageIndex.ToString() + "/" + (ImageArray.Length - 1).ToString() + " Frames.";
        }

        private int imageIndex = -1;

        public int CurrentImageIndex
        {
            get { return imageIndex; }
            //set { imageIndex = value; }
        }
        private ImageBrush[] imageBrushArray;
        private ImageBrush[] reflectionBrushArray;
        //private string[] _imageArray;

        private PathUri[] _imageArray;
        public PathUri[] ImageArray
        {
            get { return _imageArray; }
            set { _imageArray = value; }
        }
        
        int iSelectedIndex = -1;

        public int SelectedIndex
        {
            get { return iSelectedIndex; }
            set { iSelectedIndex = value; }
        }

        List<object> _items = new List<object>();

        public List<object> Items
        {
            get { return _items; }
            set { _items = value; }
        }

        public object SelectedItem
        {
            get { 
                if(iSelectedIndex != -1 && iSelectedIndex < Items.Count)
                {
                    return Items[iSelectedIndex];
                }
                return null;
            }
        }

        public event EventHandler SelectionChanged;

        public void SetActualWidthAndHeight(double iWidth, double iHeight)
        {
            bgTop.Width = iWidth;
            bgBottom.Width = iWidth;
        }
    }
}