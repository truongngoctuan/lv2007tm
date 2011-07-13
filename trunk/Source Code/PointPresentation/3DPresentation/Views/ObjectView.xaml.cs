using System;
using System.IO;
using System.Windows;
using System.Windows.Controls;
using _3DPresentation.Models;
using _3DPresentation.Views.Editor;


namespace _3DPresentation.Views
{
    public partial class ObjectView : UserControl
    {
        public bool IsLoaded { get; private set; }
        public UserControl ParentView { get; set; }
        public BaseModel Target { get; set; }
        public ObjectView()
        {
            InitializeComponent();
            this.Loaded += new RoutedEventHandler(ObjectView_Loaded);
            this.btBack.Click += new RoutedEventHandler(btBack_Click);            
            this.cbbModel.ImageSelected += new ImageSelectedEventHandler(cbbModel_ImageSelected);
        }

        void btBack_Click(object sender, RoutedEventArgs e)
        {
            App.RemovePage(this);
            
            BaseModel[] models = viewControl.GetModels();
            for (int i = 0; i < models.Length; i++)
            {
                models[i].IsEnabled = true;
            }
            models = null;

            App.GoToPage(this.ParentView);
        }

        void cbbModel_ImageSelected(object sender, ImageSelectedEventArgs e)
        {
            SetTarget((BaseModel)e.SelectedItem);
        }

        void ObjectView_Loaded(object sender, RoutedEventArgs e)
        {
            IsLoaded = true;
        }

        public void AddModels(BaseModel[] models)
        {
            for (int i = 0; i < models.Length; i++)
            {
                AddModel(models[i]);
            }
        }

        public void ClearModels()
        {
            viewControl.ClearModels();
        }

        public BaseModel GetTarget()
        {
            return Target;
        }

        public bool SetTarget(BaseModel model)
        {
            bool result = false;
            if (viewControl.SetTarget(model))
            {
                BaseModel[] models = viewControl.GetModels();
                for (int i = 0; i < models.Length; i++)
                {
                    models[i].IsEnabled = false;
                }
                Target = model;
                Target.IsEnabled = true;
                models = null;
                result = true;
            }
            return result;
        }

        private bool ImportModel(FileInfo file)
        {
            BaseModel model = BaseModel.Import(file);
            if (model == null)
                return false;

            return AddModel(model);
        }        

        private bool AddModel(BaseModel model)
        {
            bool result = false;
            if (viewControl.AddModel(model))
            {
                cbbModel.AddImage(model, model.toBitmap());
                result = true;
            }
            return result;
        }

        private bool RemoveModel(BaseModel model)
        {
            bool result = false;
            if (viewControl.RemoveModel(model))
            {
                model.IsEnabled = true;                
                result = true;
            }
            return result;
        }

        private void LayoutRoot_SizeChanged(object sender, SizeChangedEventArgs e)
        {
            cbbModel.SetActualWidthAndHeight(LayoutRoot.ActualWidth, LayoutRoot.ActualHeight);
        }
    }
}
