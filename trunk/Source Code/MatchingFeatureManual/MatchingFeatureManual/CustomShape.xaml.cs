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

namespace MatchingFeatureManual
{
    public partial class CustomShape : UserControl
    {
        Point _p1, _p2;
        Line _line;
        Ellipse _ell1, _ell2;
        public CustomShape()
        {
            InitializeComponent();

            Init();
        }
        protected void Init()
        {
            _p1 = new Point(10, 20);
            _p2 = new Point(100, 150);

            _line = new Line();
            _line.X1 = _p1.X;
            _line.Y1 = _p1.Y;
            _line.X2 = _p2.X;
            _line.Y2 = _p2.Y;
            _line.StrokeThickness = 3;
            _line.Stroke = new SolidColorBrush(Colors.Brown);

            _ell1 = new Ellipse();
            _ell1.Width = 10;
            _ell1.Height = 10;
            _ell1.Fill = new SolidColorBrush(Colors.Black);
            _ell1.SetValue(Canvas.LeftProperty, _p1.X - _ell1.Width / 2);
            _ell1.SetValue(Canvas.TopProperty, _p1.Y - _ell1.Height / 2);
            
            _ell2 = new Ellipse();
            _ell2.Width = 10;
            _ell2.Height = 10;
            _ell2.Fill = new SolidColorBrush(Colors.Gray);
            _ell2.SetValue(Canvas.LeftProperty, _p2.X - _ell2.Width / 2);
            _ell2.SetValue(Canvas.TopProperty, _p2.Y - _ell2.Height / 2);
            
            LayoutRoot.Children.Add(_ell1);
            LayoutRoot.Children.Add(_ell2);
            LayoutRoot.Children.Add(_line);

            GeometryGroup gg = new GeometryGroup();
            PathGeometry pg = new PathGeometry();
            pg.Figures = new PathFigureCollection();

            PathFigureCollection asd = new PathFigureCollection();
            PathFigure pf = new PathFigure();
        }

        private void LayoutRoot_MouseEnter(object sender, MouseEventArgs e)
        {
            //MessageBox.Show("LayoutRoot_MouseEnter");
        }
    }
}
