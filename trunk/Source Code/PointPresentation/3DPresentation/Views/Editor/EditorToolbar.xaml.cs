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

namespace _3DPresentation.Views.Editor
{
    public partial class EditorToolbar : UserControl
    {
        public EditorToolbar()
        {
            InitializeComponent();
        }
        
        private void btSetupSDK_Click(object sender, RoutedEventArgs e)
        {
            cwSetupSDK cwNew = new cwSetupSDK();
            cwNew.Show();
        }

        private void btSetupWorkSpace_Click(object sender, RoutedEventArgs e)
        {
            cwSetupWorkSpace cwNew = new cwSetupWorkSpace();
            cwNew.Show();
        }

        private void btResetWorkSpace_Click(object sender, RoutedEventArgs e)
        {
            cwResetWorkSpace cwNew = new cwResetWorkSpace();
            cwNew.Show();
        }

        private void btOpenModel_Click(object sender, RoutedEventArgs e)
        {
            cwOpenModel cwNew = new cwOpenModel();
            cwNew.Show();
        }

        private void btSaveModel_Click(object sender, RoutedEventArgs e)
        {
            cwSaveModel cwNew = new cwSaveModel();
            cwNew.Show();
        }

        private void btOptimize_Click(object sender, RoutedEventArgs e)
        {
            cwOptimize cwNew = new cwOptimize();
            cwNew.Show();
        }
    }
}
