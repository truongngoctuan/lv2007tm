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
using System.ComponentModel;

namespace _3DPresentation
{
    public partial class PropertiesPanel : UserControl
    {
        public INotifyPropertyChanged Target
        {
            get 
            {
                return (INotifyPropertyChanged)propertiesGrid.SelectedObject;
            }
            set
            {
                propertiesGrid.SelectedObject = value;
            }
            
        }

        public PropertiesPanel()
        {
            InitializeComponent();
        }
    }
}
