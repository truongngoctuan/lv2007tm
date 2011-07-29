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
using System.Windows.Navigation;

namespace _3DPresentation.Views
{
    public partial class MainView : Page
    {
        public MainView()
        {
            InitializeComponent();
        }

        // Executes when the user navigates to this page.
        protected override void OnNavigatedTo(NavigationEventArgs e)
        {
        }

        private void Button_Click(object sender, RoutedEventArgs e)
        {
            MessageBox.Show("This feature require elevated trust");
            EditorView ev = new EditorView();
            ev.ParentView = this;
            App.RemovePage(this);
            App.GoToPage(ev);
        }

        private void Button_Click_1(object sender, RoutedEventArgs e)
        {
            Catalog catalog = new Catalog();
            catalog.DesignMode = false;
            catalog.ParentView = this;
            App.RemovePage(this);
            App.GoToPage(catalog);
        }

        private void Button_Click_2(object sender, RoutedEventArgs e)
        {
            Catalog catalog = new Catalog();
            catalog.DesignMode = true;
            catalog.ParentView = this;
            App.RemovePage(this);
            App.GoToPage(catalog);
        }

    }
}
