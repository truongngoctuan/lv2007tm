using System;
using System.Windows;
using System.Windows.Controls;
using System.Windows.Documents;
using System.Windows.Ink;
using System.Windows.Input;
using System.Windows.Media;
using System.Windows.Media.Animation;
using System.Windows.Shapes;
using System.Windows.Media.Effects;

namespace MatchingFeatureManual
{
	public partial class Feature : UserControl
	{
        static int ELLIPSE_WIDTH = 10;
        static int ELLIPSE_HEIGHT = 10;
        bool bIsSelected = false;
        public bool getIsSelected()
        {
            return bIsSelected;
        }

        public void setIsSelected(bool value)
        {
            bIsSelected = value;
            if (bIsSelected)
            {
                P1.Opacity = 1;
                P2.Opacity = 1;
                li.Opacity = 1;
                li.Stroke = new SolidColorBrush(Colors.LightGray);

                int iTopZ = 0;
                int iTempZ;
                foreach (UIElement element in _parent.LayoutRoot.Children)
                {
                     iTempZ = Canvas.GetZIndex(element);
                     if (iTopZ < iTempZ)
                     {
                         iTopZ = iTempZ;
                     }
                }

                Canvas.SetZIndex(li, iTopZ + 1);
                Canvas.SetZIndex(P1, iTopZ + 2);
                Canvas.SetZIndex(P2, iTopZ + 3);

                _parent.FeatureSelected = this;
            }
            else
            {
                P1.Opacity = 0.5;
                P2.Opacity = 0.5;
                li.Opacity = 0.5;
                li.Stroke = new SolidColorBrush(Colors.Black);
            }
        }

        Line li = new Line();
        Ellipse P1 = new Ellipse();
        Ellipse P2 = new Ellipse();

        #region center + topleft point
        /// <summary>
        /// 4 var manager position topleft and center of 2 main points of pair
        /// </summary>
        Point CenterPositionP1;
        public Point CenterP1
        {
            get { return CenterPositionP1; }
            set { CenterPositionP1 = value;
            TopLeftPositionP1 = Feature.CenterToTopLeft(CenterP1);
            }
        }

        Point CenterPositionP2;
        public Point CenterP2
        {
            get { return CenterPositionP2; }
            set { CenterPositionP2 = value;
            TopLeftPositionP2 = Feature.CenterToTopLeft(CenterP2);
            }
        }

        Point TopLeftPositionP1;
        public Point TopLeftP1
        {
            get { return TopLeftPositionP1; }
            set { TopLeftPositionP1 = value;
            CenterPositionP1 = Feature.TopLeftToCenter(TopLeftPositionP1);
            }
        }

        Point TopLeftPositionP2;
        public Point TopLeftP2
        {
            get { return TopLeftPositionP2; }
            set { TopLeftPositionP2 = value;
            CenterPositionP2 = Feature.TopLeftToCenter(TopLeftPositionP2);
            }
        }
        #endregion

        CanvasFeaturePair _parent;

        public Feature(Point point1, Point point2)
		{
			// Required to initialize variables
			InitializeComponent();

            P1.Width = ELLIPSE_WIDTH;
            P1.Height = ELLIPSE_HEIGHT;
            P1.Fill = new SolidColorBrush(Colors.White);
            P1.Stroke = new SolidColorBrush(Colors.Black);
            P1.Opacity = 0.5;
            CenterP1 = point1;

            P2.Width = ELLIPSE_WIDTH;
            P2.Height = ELLIPSE_HEIGHT;
            P2.Fill = new SolidColorBrush(Colors.White);
            P2.Stroke = new SolidColorBrush(Colors.Black);
            P2.Opacity = 0.5;
            CenterP2 = point2;

            li.X1 = CenterP1.X;
            li.Y1 = CenterP1.Y;
            li.X2 = CenterP2.X;
            li.Y2 = CenterP2.Y;
            li.StrokeThickness = 5;
            li.Stroke = new SolidColorBrush(Colors.Black);
            li.Opacity = 0.5;

            //BlurEffect be = new BlurEffect();
            //li.Effect = new BlurEffect { Radius = 5};

            P1.MouseLeftButtonDown += new MouseButtonEventHandler(Ellipse_MouseLeftButtonDownPoint1);
            P1.MouseLeftButtonUp += new MouseButtonEventHandler(Ellipse_MouseLeftButtonUpPoint1);

            P2.MouseLeftButtonDown += new MouseButtonEventHandler(Ellipse_MouseLeftButtonDownPoint2);
            P2.MouseLeftButtonUp += new MouseButtonEventHandler(Ellipse_MouseLeftButtonUpPoint2);

            li.MouseLeftButtonDown += new MouseButtonEventHandler(li_MouseLeftButtonDown);
            li.MouseLeftButtonUp += new MouseButtonEventHandler(li_MouseLeftButtonUp);
		}

        #region handler Line
        bool bIsLineMouseDown = false;

        void li_MouseLeftButtonDown(object sender, MouseButtonEventArgs e)
        {
            // TODO: Add event handler implementation here.
            setIsSelected(true);
            oldPoint = e.GetPosition(_parent);
            bIsLineMouseDown = true;

            //add listener into parent
            _parent.MouseMove += new MouseEventHandler(FeatureLine_MouseMove);
        }

        void li_MouseLeftButtonUp(object sender, MouseButtonEventArgs e)
        {
            bIsLineMouseDown = false;

            //remove listener
            _parent.MouseMove -= FeatureLine_MouseMove;

            Point newpoint = e.GetPosition(_parent);
        }

        private void FeatureLine_MouseMove(object sender, System.Windows.Input.MouseEventArgs e)
        {
            try
            {
                // TODO: Add event handler implementation here.
                if (bIsLineMouseDown)
                {
                    Point newPoint = e.GetPosition(_parent);
                    Point OffsetPosition = new Point(newPoint.X - oldPoint.X, newPoint.Y - oldPoint.Y);

                    MoveP1OffsetPosition(OffsetPosition);
                    MoveP2OffsetPosition(OffsetPosition);

                    oldPoint = newPoint;
                }
            }
            catch (Exception ex)
            {
                MessageBox.Show("FeatureLine_MouseMove: " + ex.Message);
            }
        }
        #endregion

        #region attach and detach to customcanvas
        public void AttachTo(CanvasFeaturePair parent)
        {
            Canvas.SetLeft(P1, TopLeftP1.X);
            Canvas.SetTop(P1, TopLeftP1.Y);

            Canvas.SetLeft(P2, TopLeftP2.X);
            Canvas.SetTop(P2, TopLeftP2.Y);

            parent.LayoutRoot.Children.Add(li);
            parent.LayoutRoot.Children.Add(P1);
            parent.LayoutRoot.Children.Add(P2);

            _parent = parent;
        }

        public void Detach()
        {
            _parent.LayoutRoot.Children.Remove(P2);
            _parent.LayoutRoot.Children.Remove(P1);
            _parent.LayoutRoot.Children.Remove(li);
        }

        #endregion

        Point oldPoint;
        bool bIsMouseDown = false;
        bool IsPoint1Down = false;
        private void Ellipse_MouseLeftButtonDownPoint1(object sender, System.Windows.Input.MouseButtonEventArgs e)
        {
            // TODO: Add event handler implementation here.
            setIsSelected(true);
            oldPoint = e.GetPosition(_parent);
            bIsMouseDown = true;

            IsPoint1Down = true;

            //add listener into parent
            _parent.MouseMove += new MouseEventHandler(Ellipse_MouseMove);
        }

        private void Ellipse_MouseLeftButtonUpPoint1(object sender, MouseButtonEventArgs e)
        {
            bIsMouseDown = false;

            //remove listener
            _parent.MouseMove -= Ellipse_MouseMove;

            Point newpoint = e.GetPosition(_parent);
        }

        private void Ellipse_MouseLeftButtonDownPoint2(object sender, System.Windows.Input.MouseButtonEventArgs e)
        {
            // TODO: Add event handler implementation here.
            setIsSelected(true);
            oldPoint = e.GetPosition(_parent);
            bIsMouseDown = true;
            IsPoint1Down = false;

            //add listener into parent
            _parent.MouseMove += new MouseEventHandler(Ellipse_MouseMove);
        }

        private void Ellipse_MouseLeftButtonUpPoint2(object sender, MouseButtonEventArgs e)
        {
            bIsMouseDown = false;

            //remove listener
            _parent.MouseMove -= Ellipse_MouseMove;

            Point newpoint = e.GetPosition(_parent);
        }

        private void Ellipse_MouseMove(object sender, System.Windows.Input.MouseEventArgs e)
        {
            try
            {
                // TODO: Add event handler implementation here.
                if (bIsMouseDown)
                {
                    Point newPoint = e.GetPosition(_parent);

                    if (IsPoint1Down)
                    {
                        Point OffsetPosition = new Point(newPoint.X - oldPoint.X, newPoint.Y - oldPoint.Y);
                        MoveP1OffsetPosition(OffsetPosition);
                    }
                    else
                    {
                        Point OffsetPosition = new Point(newPoint.X - oldPoint.X, newPoint.Y - oldPoint.Y);
                        MoveP2OffsetPosition(OffsetPosition);
                    }
                    oldPoint = newPoint;
                }
            }
            catch (Exception ex)
            {
                MessageBox.Show("Ellipse_MouseMove: " + ex.Message);
            }
        }

        #region animation

        Storyboard stFeature = null;
        Storyboard stLine = null;
        DoubleAnimation daLeft;
        DoubleAnimation daTop;

        DoubleAnimation daLeftLine;
        DoubleAnimation daTopLine;

        public void MoveP1OffsetPosition(Point offsetPoint)
        {
            //update main point 1
            TopLeftP1 = new Point(TopLeftP1.X + offsetPoint.X, TopLeftP1.Y + offsetPoint.Y);

            Canvas.SetLeft(P1, TopLeftP1.X);
            Canvas.SetTop(P1, TopLeftP1.Y);

            li.X1 = CenterP1.X;
            li.Y1 = CenterP1.Y;

            AnimationMove(P1, li, TopLeftP1, true);
        }

        public void MoveP2OffsetPosition(Point offsetPoint)
        {
            TopLeftP2 = new Point(TopLeftP2.X + offsetPoint.X, TopLeftP2.Y + offsetPoint.Y);

            Canvas.SetLeft(P2, TopLeftP2.X);
            Canvas.SetTop(P2, TopLeftP2.Y);

            li.X2 = CenterP2.X;
            li.Y2 = CenterP2.Y;

            AnimationMove(P2, li, TopLeftP2, false);
        }

        public void MoveP1CenterPosition(Point centerPoint)
        {
            //update main point 1
            CenterP1 = centerPoint;

            Canvas.SetLeft(P1, TopLeftP1.X);
            Canvas.SetTop(P1, TopLeftP1.Y);

            li.X1 = CenterP1.X;
            li.Y1 = CenterP1.Y;

            AnimationMove(P1, li, TopLeftP1, true);
        }

        public void MoveP2CenterPosition(Point centerPoint)
        {
            CenterP2 = centerPoint;

            Canvas.SetLeft(P2, TopLeftP2.X);
            Canvas.SetTop(P2, TopLeftP2.Y);

            li.X2 = CenterP2.X;
            li.Y2 = CenterP2.Y;

            AnimationMove(P2, li, TopLeftP2, false);
        }
        void AnimationMove(UIElement elementPoint1, UIElement elementLine, Point newTopLeftCanvas, bool bIsMovePoint1)
        {
            SetAnimationPoint(elementPoint1, newTopLeftCanvas, 250,
                out daLeft, out daTop,
                "Canvas.Left", "Canvas.Top");

            if (bIsMovePoint1)
            {
                SetAnimationPoint(elementLine, Feature.TopLeftToCenter(newTopLeftCanvas), 250,
                    out daLeftLine, out daTopLine,
                    "X1", "Y1");
            }
            else
            {
                SetAnimationPoint(elementLine, Feature.TopLeftToCenter(newTopLeftCanvas), 250,
                    out daLeftLine, out daTopLine,
                    "X2", "Y2");
            }

            stFeature = new Storyboard();
            stFeature.Children.Add(daLeft);
            stFeature.Children.Add(daTop);
            stFeature.Begin();

            stLine = new Storyboard();
            stLine.Children.Add(daLeftLine);
            stLine.Children.Add(daTopLine);
            stLine.Begin();

        }

        private static void SetAnimationPoint(UIElement element, Point newPoint1, int iMiliSecond,
            out DoubleAnimation Left, out DoubleAnimation Top,
            string strPropertiesX, string strPropertiesY)
        {
            Left = new DoubleAnimation();
            Left.To = newPoint1.X;
            Left.Duration = new Duration(new TimeSpan(0, 0, 0, 0, iMiliSecond));

            Top = new DoubleAnimation();
            Top.To = newPoint1.Y;
            Top.Duration = new Duration(new TimeSpan(0, 0, 0, 0, iMiliSecond));

            // Set the storyboard target and target property
            Storyboard.SetTarget(Left, element);
            Storyboard.SetTargetProperty(Left, new PropertyPath("(" + strPropertiesX + ")"));

            Storyboard.SetTarget(Top, element);
            Storyboard.SetTargetProperty(Top, new PropertyPath("(" + strPropertiesY + ")"));
        }
        #endregion

        public static Point TopLeftToCenter(Point TopLeft)
        {
            return new Point(TopLeft.X + ELLIPSE_WIDTH / 2, TopLeft.Y + ELLIPSE_HEIGHT / 2);
        }

        public static Point CenterToTopLeft(Point Center)
        {
            return new Point(Center.X - ELLIPSE_WIDTH / 2, Center.Y - ELLIPSE_HEIGHT / 2);
        }
        
        public override bool Equals(object obj)
        {
            if (obj != null)
            {
                //return base.Equals(obj);
                Feature temp = (Feature)obj;
                if (this.CenterP1.Equals(temp.CenterP1) &&
                    this.CenterP2.Equals(temp.CenterP2))
                    return true;
                return false;
            }
            return false;
        }
	}
}