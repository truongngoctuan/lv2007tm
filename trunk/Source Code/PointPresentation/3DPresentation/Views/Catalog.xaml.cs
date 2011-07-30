using System;
using System.IO;
using System.Windows.Controls;
using System.Windows;
using System.Collections.Generic;
using _3DPresentation.Data;
using System.Windows.Media.Imaging;

namespace _3DPresentation.Views
{
    public partial class Catalog : UserControl
    {
        public UserControl ParentView { get; set; }
        public Catalog()
        {
            InitializeComponent();
            this.Loaded += new RoutedEventHandler(Catalog_Loaded);
            this.btBack.Click += new RoutedEventHandler(btBack_Click);
            this.btNewTour.Click += new RoutedEventHandler(btNewTour_Click);
            this.btDelAll.Click += new RoutedEventHandler(btDelAll_Click);
        }

        List<string> tourList;
        void UpdateList()
        {
            tourList = new List<string>(Utils.Global.GetTourList());

            stackPanel.Children.Clear();
            foreach (string tour in tourList)
            {
                Button bt = new Button();
                bt.Background = new System.Windows.Media.SolidColorBrush(System.Windows.Media.Color.FromArgb(255, 0, 0, 0));
                bt.Width = 225;
                bt.Height = 50;
                bt.Foreground = new System.Windows.Media.SolidColorBrush(System.Windows.Media.Color.FromArgb(255, 0, 0, 255));
                bt.FontSize = 20;
                bt.Content = tour;
                bt.Click += new RoutedEventHandler(bt_Click);

                stackPanel.Children.Add(bt);
            }
        }

        void btDelAll_Click(object sender, RoutedEventArgs e)
        {
            Utils.Global.DeleteAllTours();
            UpdateList();
        }

        void btNewTour_Click(object sender, RoutedEventArgs e)
        {
            if (tbNewTourName.Text.Length == 0 || tourList.Contains(tbNewTourName.Text))
                return;

            Tour tour = new Tour();
            tour.Name = tbNewTourName.Text;
            tour.SceneName = "espilit";
            if (tour.Save())
            {
                UpdateList();
            }
        }

        void btBack_Click(object sender, RoutedEventArgs e)
        {
            if (ParentView != null)
            {
                App.RemovePage(this);
                App.GoToPage(ParentView);
            }
        }

        string GetName(string filename)
        {
            string name = null;
            int dotIndex = filename.LastIndexOf('.');
            int slashIndex = filename.LastIndexOf('/');
            if(slashIndex < dotIndex)
            {
                name = filename.Substring(slashIndex + 1, dotIndex - slashIndex - 1); 
            }
            return name;
        }

        void Catalog_Loaded(object sender, RoutedEventArgs e)
        {
            UpdateList();
        }

        bool _designMode = false;
        public bool DesignMode 
        {
            get { return _designMode; }
            set 
            { 
                _designMode = value; 
                btNewTour.Visibility = _designMode ? System.Windows.Visibility.Visible : System.Windows.Visibility.Collapsed;
                btDelAll.Visibility = _designMode ? System.Windows.Visibility.Visible : System.Windows.Visibility.Collapsed; 
				tbNewTourName.Visibility = _designMode ? System.Windows.Visibility.Visible : System.Windows.Visibility.Collapsed; 
            }
        }

        void bt_Click(object sender, RoutedEventArgs e)
        {
            if (DesignMode)
            {
                TourDesign tourDesign = new TourDesign();
                tourDesign.TourName = (string)(((Button)sender).Content);
                tourDesign.ParentView = this;
                App.RemovePage(this);
                App.GoToPage(tourDesign);
            }
            else
            {
                TourView tourView = new TourView();
                tourView.TourName = (string)(((Button)sender).Content);
                tourView.ParentView = this;
                App.RemovePage(this);
                App.GoToPage(tourView);
            }
        }
    }
}
