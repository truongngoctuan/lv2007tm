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
using _3DPresentation.Models;

namespace _3DPresentation
{
    public partial class ViewControl : UserControl
    {
        public UserControl ParentView { get; set; }
        public bool IsLoaded { get; private set; }

        ViewScene viewScene;
        public ViewControl()
        {
            InitializeComponent();
            this.Loaded += new RoutedEventHandler(ViewControl_Loaded);
            viewScene = new ViewScene(this, drawingSurface);

            cbModels.SelectionChanged += new SelectionChangedEventHandler(cbModels_SelectionChanged);
        }

        void ViewControl_Loaded(object sender, RoutedEventArgs e)
        {
            IsLoaded = true;
        }

        void cbModels_SelectionChanged(object sender, SelectionChangedEventArgs e)
        {
            SetTarget((BaseModel)cbModels.SelectedItem);
        }

        public BaseModel GetTarget()
        {
            return viewScene.TargetModel;
        }

        public bool SetTarget(BaseModel model)
        {
            return viewScene.SetTarget(model);
        }

        public bool AddModel(BaseModel model)
        {
            bool result = viewScene.AddModel(model);
            if (result == false)
                return false;
            cbModels.Items.Add(model);
            return true;
        }

        public bool RemoveModel(BaseModel model)
        {
            bool result = viewScene.RemoveModel(model);
            if (result == false)
                return false;
            cbModels.Items.Remove(model);
            return true;
        }

        public void ClearModels()
        {
            viewScene.ClearModels();
            cbModels.Items.Clear();
        }
    }
}
