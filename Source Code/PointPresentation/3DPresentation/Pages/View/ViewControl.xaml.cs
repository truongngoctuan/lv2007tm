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
using _3DPresentation.Views.Editor;

namespace _3DPresentation
{
    public partial class ViewControl : UserControl
    {        
        public UserControl ParentView { get; set; }
        public bool IsLoaded { get; private set; }

        ViewScene viewScene;

        public ViewScene ViewScene
        {
            get { return viewScene; }
            set { viewScene = value; }
        }
        public ViewControl()
        {
            InitializeComponent();
            this.Loaded += new RoutedEventHandler(ViewControl_Loaded);
            viewScene = new ViewScene(this, drawingSurface);

            //cbModels.SelectionChanged += new SelectionChangedEventHandler(cbModels_SelectionChanged);
            //cbModels.SelectionChanged +=new EventHandler(cbModels_SelectionChanged);
        }

        void ViewControl_Loaded(object sender, RoutedEventArgs e)
        {
            IsLoaded = true;
        }

        //void cbModels_SelectionChanged(object sender, EventArgs e)
        //{
        //    SetTarget((BaseModel)cbModels.SelectedItem);
        //}

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
            //cbModels.Items.Add(model);
            //cbModels.AddImage(model, new PathUri(_3DPresentation.Utils.Global.GetRandomSnapshot(), false));
            return true;
        }

        public bool RemoveModel(BaseModel model)
        {
            bool result = viewScene.RemoveModel(model);
            if (result == false)
                return false;
            //cbModels.Items.Remove(model);
            return true;
        }

        public void ClearModels()
        {
            viewScene.ClearModels();
            //cbModels.Items.Clear();
        }

        public Color BackgoundColor
        {
            get {
                return ((SolidColorBrush)LayoutRoot.Background).Color;
            }
            set
            {
                LayoutRoot.Background = new SolidColorBrush(value);
            }
        }
    }
}
