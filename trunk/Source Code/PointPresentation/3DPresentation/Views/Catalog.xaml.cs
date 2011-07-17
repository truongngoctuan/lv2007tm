using System;
using System.IO;
using System.Windows.Controls;
using System.Windows;
using System.Collections.Generic;
using _3DPresentation.Data;

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
        }

        List<string> toursName = null;
        void btNewTour_Click(object sender, RoutedEventArgs e)
        {
            Tour tour = new Tour();
            tour.Name = DateTime.Now.Ticks.ToString();
            tour.SceneName = "espilit";
            if (tour.Save())
            {
                Button bt = new Button();
                bt.Content = tour.Name;
                bt.Click += new RoutedEventHandler(bt_Click);

                stackPanel.Children.Add(bt);
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
            toursName = new List<string>();
            DirectoryInfo dirInfo = Utils.Global.GetRealDirectory(Utils.Global.GetRealTourStorePath());
            if (dirInfo == null)
                return;
            foreach (DirectoryInfo tourDir in dirInfo.EnumerateDirectories())
            {
                foreach (FileInfo tour in tourDir.EnumerateFiles("*.tour"))
                {
                    string name = GetName(tour.Name);
                    if (name == tourDir.Name)
                    {
                        toursName.Add(name);
                    }
                }
            }

            stackPanel.Children.Clear();
            foreach (string tour in toursName)
            {
                Button bt = new Button();
                bt.Content = tour;
                bt.Click += new RoutedEventHandler(bt_Click);

                stackPanel.Children.Add(bt);
            }
        }

        bool _designMode = false;
        public bool DesignMode 
        {
            get { return _designMode; }
            set { _designMode = value; btNewTour.Visibility = _designMode ? System.Windows.Visibility.Visible : System.Windows.Visibility.Collapsed; }
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
