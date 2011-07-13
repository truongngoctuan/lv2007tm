using System;
using System.IO;
using System.Windows;
using System.Windows.Controls;
using _3DPresentation.Models;
using _3DPresentation.Views.Editor;

namespace _3DPresentation.Views
{
    public partial class ObjectDesign : UserControl
    {
        public bool IsLoaded { get; private set; }
        public UserControl ParentView { get; set; }
        public BaseModel Target { get; set; }
        public ObjectDesign()
        {
            InitializeComponent();
            this.Loaded += new RoutedEventHandler(ObjectDesign_Loaded);
            this.cbbModel.ImageSelected += new ImageSelectedEventHandler(cbbModel_ImageSelected);
        }

        void cbbModel_ImageSelected(object sender, ImageSelectedEventArgs e)
        {
            SetTarget((BaseModel)cbbModel.SelectedItem);
        }

        void ObjectDesign_Loaded(object sender, RoutedEventArgs e)
        {
            IsLoaded = true;
            //ExecuteScript("abc");
        }

        public bool ExecuteScript(string strScript)
        {
            if (IsLoaded == false)
                return false;
            ImportModel(new FileInfo(Utils.Global.StorePath + "/Scene/espilit/Models/" + "kit_face.ply"));
            return true;
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
                if(Target != null)
                    Target.IsEnabled = false;

                Target = model;
                materialSelector.SetTarget(Target);
                Target.IsEnabled = true;
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
                model.IsEnabled = false;
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
