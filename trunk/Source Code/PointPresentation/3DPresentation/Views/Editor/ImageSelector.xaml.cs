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
using System.Collections.Generic;
using System.IO;

namespace _3DPresentation.Views.Editor
{
    public class ImageSelectedEventArgs : EventArgs
    {
        public BitmapImage Source;
        public int SelectedIndex;
    }

    public delegate void ImageSelectedEventHandler(object sender, ImageSelectedEventArgs e);

    public class PathUri
    {
        public PathUri(string str, bool b)
        {
            Path = str;
            IsAbsolutePath = b;
        }
        public string Path;
        public bool IsAbsolutePath;

        public BitmapImage toBitmapImage()
        {
            if (IsAbsolutePath)
            {
                return _3DPresentation.Utils.Global.AbsolutePathStringToBitmapImage(Path);
            }
            else
            {
                return new BitmapImage(_3DPresentation.Utils.Global.MakePackUri(Path));
            }
        }
    }

    public partial class ImageSelector : UserControl
    {
        public event ImageSelectedEventHandler ImageSelected;

        public ImageSelector()
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

            btTestAdd.Click += new RoutedEventHandler(btTestAdd_Click);

            this.SetImages(new PathUri[] {});
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

        public void AddImage(PathUri strFileName)
        {
            try
            {
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
                        MoveBack();
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
                        MoveBack();
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
                if (realLength <= 7)
                {
                    List<PathUri> arr = new List<PathUri>();
                    for (int i = 0; i < realLength; i++)
                    {
                        arr.Add(ImageArray[i]);
                    }
                    arr.RemoveAt(iIndex);
                    realLength--;

                    for (int i = 0; i < 7 - realLength; i++)
                    {
                        arr.Add(new PathUri("Views/Editor/Images/blank.jpg", false));
                    }
                    ImageArray = arr.ToArray();

                    if ((realLength != imageIndex && realLength == iIndex) || imageIndex == 0)
                    {//this branch do not update imageindex, just update brushindex, because real length change
                        brushIndex = (imageIndex + ImageArray.Length - 3) % ImageArray.Length;

                        UpdateImages();
                        return;
                    }

                    if (realLength == imageIndex)
                    {//have effect forward coverflow
                        MoveForward();
                        return;
                    }

                    if (iIndex < imageIndex)
                    {
                        MoveForward();
                        return;
                    }

                    MoveForward(false);

                }
                else
                {
                    List<PathUri> arr = new List<PathUri>();
                    for (int i = 0; i < realLength; i++)
                    {
                        arr.Add(ImageArray[i]);
                    }
                    arr.RemoveAt(iIndex);
                    realLength--;
                    ImageArray = arr.ToArray();
                    
                    if ((realLength != imageIndex && realLength == iIndex) || iIndex == 0)
                    {//this branch do not update imageindex, just update brushindex, because real length change
                        brushIndex = (imageIndex + ImageArray.Length - 3) % ImageArray.Length;

                        UpdateImages();
                        return;
                    }

                    if (realLength == imageIndex)
                    {//have effect forward coverflow
                        MoveForward();
                        return;
                    }

                    if (iIndex < imageIndex)
                    {
                        MoveForward();
                        return;
                    }

                    MoveForward(false);

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
            if (SelectedIndex >= realLength || SelectedIndex < 0) return;
            ImageSelectedEventArgs args = new ImageSelectedEventArgs();
            args.Source = (BitmapImage)((ImageBrush)((System.Windows.Shapes.Path)sender).Fill).ImageSource;
            args.SelectedIndex = SelectedIndex;
            SelectedIndex = -1;
            //MessageBox.Show(SelectedIndex.ToString());
            ClickedPositionParent = e.GetPosition(_parent);
            OnImageSelected(args);            
        }

        void btTestAdd_Click(object sender, RoutedEventArgs e)
        {
            //throw new NotImplementedException();
            try
            {
                this.AddImage(new PathUri("Views/Editor/Images/j0149013.jpg", false));
            }
            catch (Exception ex)
            {
                MessageBox.Show(ex.Message);
            }
        }

        protected void OnImageSelected(ImageSelectedEventArgs e)
        {
            if (ImageSelected != null)
            {
                ImageSelected(this, e);
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

                MoveBack();
            }
        }

        void btnForward_Click(object sender, EventArgs e)
        {
            if (imageIndex != -1)
            {
                if (imageIndex == 0 && realLength < 7) return;
                MoveForward();
            }
        }

        #region Move

        void MoveBack(bool UseAnimation = true)
        {
            if (UseAnimation)
            {
                firstImgBrush.ImageSource = ImageArray[brushIndex].toBitmapImage();
                firstReflectionBrush.ImageSource = ImageArray[brushIndex].toBitmapImage();
            }

            imageIndex = (++imageIndex + ImageArray.Length) % ImageArray.Length;
            brushIndex = (imageIndex + ImageArray.Length - 3) % ImageArray.Length;

            UpdateImages();

            if (UseAnimation)
            {
                flowBackward.Begin();
            }
        }

        void MoveForward(bool UseAnimation = true)
        {
            if (UseAnimation)
            {
                lastImgBrush.ImageSource = ImageArray[(brushIndex + 6) % ImageArray.Length].toBitmapImage();
                lastReflectionBrush.ImageSource = ImageArray[(brushIndex + 6) % ImageArray.Length].toBitmapImage();
            }

            imageIndex = (--imageIndex + ImageArray.Length) % ImageArray.Length;
            brushIndex = (imageIndex + ImageArray.Length - 3) % ImageArray.Length;

            UpdateImages();

            if (UseAnimation)
            {
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
        #endregion


        void SetCurrentInfoFrame()
        {
            tbCurrentFrameIndex.Text = (imageIndex + 1).ToString() + "/" + (realLength).ToString() + " Frames.";
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
        
        EditorView _parent;

        public EditorView ParentView
        {
            get { return _parent; }
            set { _parent = value; }
        }
        Point _pClickedPositionParent;

        public Point ClickedPositionParent
        {
            get { return _pClickedPositionParent; }
            set { _pClickedPositionParent = value; }
        }

        int iSelectedIndex = -1;

        public int SelectedIndex
        {
            get { return iSelectedIndex; }
            set { iSelectedIndex = value; }
        }
    }
}
