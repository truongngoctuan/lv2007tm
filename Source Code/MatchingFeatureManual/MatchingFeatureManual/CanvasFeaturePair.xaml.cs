using System;
using System.Windows;
using System.Windows.Controls;
using System.Windows.Documents;
using System.Windows.Ink;
using System.Windows.Input;
using System.Windows.Media;
using System.Windows.Media.Animation;
using System.Windows.Shapes;
using System.IO;
using System.Collections.Generic;

namespace MatchingFeatureManual
{
	public partial class CanvasFeaturePair : UserControl
	{
        Feature _featureSelected = null;

        public Feature FeatureSelected
        {
            get { return _featureSelected; }
            set {
                if (_featureSelected != null)
                {
                    if (!_featureSelected.Equals(value))
                    {
                        _featureSelected.setIsSelected(false);
                        _featureSelected = value;
                    }
                    else
                    {
                    }
                }
                else
                {
                    _featureSelected = value;
                }
            }
        }

		public CanvasFeaturePair()
		{
			// Required to initialize variables
			InitializeComponent();

            ReadFromFile("d:\\pairs.txt");

		}

        //private void Button_Click(object sender, RoutedEventArgs e)
        //{
        //    //load img from local
        //    //http://blogs.silverlight.net/blogs/msnow/archive/2009/02/09/silverlight-tip-of-the-day-92-how-to-load-images-from-a-stream.aspx

        //    //Configure an Application for Out-of-Browser Support 
        //    //bổ sung thêm trong AppManifest.xml để chạy đc code này
        //    //http://msdn.microsoft.com/en-us/library/dd833073%28v=VS.96%29.aspx
        //    //http://msdn.microsoft.com/en-us/library/gg192793%28v=VS.96%29.aspx
        //        BitmapImage bi = new BitmapImage();

        //        FileInfo fio = new FileInfo("D:\\test.png");
        //        System.IO.Stream stream2 = fio.OpenRead();
        //        bi.SetSource(stream2);

        //        //MyImage.Source = bi;

        //        stream2.Close();

        //        Line li = new Line();
        //        li.X1 = 20;
        //        li.Y1 = 30;
        //        li.X2 = 100;
        //        li.Y2 = 150;
        //        li.StrokeThickness = 10;

        //        SolidColorBrush redBrush = new SolidColorBrush();

        //        redBrush.Color = Colors.Red;
        //        li.Stroke = redBrush;
        //        LayoutRoot.Children.Add(li);


        //}

        public enum CanvasPairState { Normal, AddingNewPair }
        CanvasPairState state = CanvasPairState.Normal;
        private void asd_Click(object sender, RoutedEventArgs e)
        {

        }

        Point[] arrP1;
        Point[] arrP2;

        //Feature[] arrf1;
        List<Feature> listFeature = new List<Feature>();


        //bool bIsLeftButtonDown = false;
        //DateTime dtLeftButtonDown;
        int ClickCount = 0;
        Point oldPoint;
        private void LayoutRoot_MouseLeftButtonDown(object sender, MouseButtonEventArgs e)
        {
            if (state == CanvasPairState.AddingNewPair)
            {
                oldPoint = e.GetPosition(LayoutRoot);
            }
        }

        Feature fAdd;
        private void LayoutRoot_MouseLeftButtonUp(object sender, MouseButtonEventArgs e)
        {
            if (state == CanvasPairState.AddingNewPair)
            {
                Point newPoint = e.GetPosition(LayoutRoot);
                if (newPoint.X == oldPoint.X &&
                    newPoint.Y == oldPoint.Y)
                {
                    ClickCount++;
                    tbClickCount.Text = ClickCount.ToString();
                }

                oldPoint = newPoint;

                if (ClickCount == 1)
                {
                    //set P1
                    fAdd = new Feature(oldPoint, oldPoint);
                    fAdd.AttachTo(this);
                }

                if (ClickCount == 2)
                {
                    //set P2
                    fAdd.MoveP2CenterPosition(oldPoint);
                    state = CanvasPairState.Normal;
                    ClickCount = 0;
                    tbClickCount.Text = ClickCount.ToString();
                }
            }
        }

        private void LayoutRoot_MouseMove(object sender, MouseEventArgs e)
        {
            if (state == CanvasPairState.AddingNewPair)
            {
                if (ClickCount == 1)
                {
                    Point newPoint = e.GetPosition(LayoutRoot);

                    fAdd.MoveP2OffsetPosition(new Point(newPoint.X - oldPoint.X, newPoint.Y - oldPoint.Y));

                    oldPoint = newPoint;
                }
            }
        }

        public void DeleteSelectedFeature()
        {
            if (this.FeatureSelected != null)
            {
                this.FeatureSelected.Detach();
                //this.LayoutRoot.Children.Remove(this.FeatureSelected);

                listFeature.Remove(this.FeatureSelected);
                this.FeatureSelected = null;
            }
        }

        public void AddNewPair()
        {
            //active state add a new pairs
            state = CanvasPairState.AddingNewPair;
            ClickCount = 0;
            //click 1: set P1, P2 move follow cursor
            //click 2: set P2, set state to normal
        }

        public void Clear()
        {
            foreach (Feature f in listFeature)
            {
                f.Detach();
            }
        }

        public void ReadFromFile(string strFileName)
        {
            StreamReader sr = new StreamReader(new FileStream(strFileName, FileMode.Open, FileAccess.Read));

            string strBuffer = sr.ReadLine();

            int iSize = int.Parse(strBuffer);
            arrP1 = new Point[iSize];
            arrP2 = new Point[iSize];

            for (int i = 0; i < iSize; i++)
            {
                strBuffer = sr.ReadLine();
                string[] strSplit = strBuffer.Split(new char[] { ' ' });

                arrP1[i].X = int.Parse(strSplit[0]);
                arrP1[i].Y = int.Parse(strSplit[1]);

                arrP2[i].X = int.Parse(strSplit[2]);
                arrP2[i].Y = int.Parse(strSplit[3]);
            }

            sr.Close();

            //arrf1 = new Feature[arrP1.Length];
            for (int i = 0; i < arrP1.Length; i++)
            {
                //arrf1[i] = new Feature(arrP1[i], new Point(arrP2[i].X + 640, arrP2[i].Y));
                //arrf1[i].AddToParent(this);

                Feature fTemp = new Feature(arrP1[i], new Point(arrP2[i].X + 640, arrP2[i].Y));
                fTemp.AttachTo(this);
                listFeature.Add(fTemp);
            }
            //LayoutRoot.InvalidateArrange();
        }

        public void SaveToFile(string strFileName)
        {
            StreamWriter sw = new StreamWriter(new FileStream(strFileName, FileMode.OpenOrCreate, FileAccess.Write));

            string strBuffer = string.Empty;
            sw.WriteLine(listFeature.Count.ToString());
            foreach (Feature f in listFeature)
            {
                sw.Write(f.CenterP1.X.ToString() + " " + f.CenterP1.Y.ToString() + " ");
                sw.WriteLine((f.CenterP2.X - 640).ToString() + " " + f.CenterP2.Y.ToString());
            }

            sw.Close();
        }
	}
}