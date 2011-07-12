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
    public partial class customChildWindow : Page
    {
        UserControl _parentView = null;

        public UserControl ParentView
        {
            get { return _parentView; }
            set { _parentView = value; }
        }

        public customChildWindow()
        {
            InitializeComponent();
        }

        // Executes when the user navigates to this page.
        protected override void OnNavigatedTo(NavigationEventArgs e)
        {
        }

        
        private void Page_SizeChanged(object sender, SizeChangedEventArgs e)
        {
            if (ParentView != null)
            {
                this.Width = ParentView.ActualWidth;
                this.Height = ParentView.ActualHeight;

                recBackground.Width = this.Width;
                recBackground.Height = this.Height;
            }
        }

        public void Show(UserControl parent)
        {
            ParentView = parent;
            App.GoToPage(this);
        }

        public void Close()
        {
            App.RemovePage(this);
            App.GoToPage(ParentView);
        }

        public void AddContent(UserControl content)
        {
            borderDlg.Child = content;
        }

        private void Button_Click(object sender, RoutedEventArgs e)
        {
            this.Close();
        }

        internal void AddContent(UIElement uIElement)
        {
            //throw new NotImplementedException();
            borderDlg.Child = uIElement;
        }
    }
}
