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
        public ObjectView()
        {
            InitializeComponent();
            this.Loaded += new RoutedEventHandler(ObjectView_Loaded);
            //this.cbbModel.ImageSelected += new ImageSelectedEventHandler(cbbModel_ImageSelected);

            this.viewControl.ViewScene.MouseRotated += new MouseRotatedEventHandler(ViewScene_MouseRotated);
            this.viewControl.ViewScene.KeyboardTransition += new KeyboardTransitionEventHandler(ViewScene_KeyboardTransition);
        }

        void ViewScene_KeyboardTransition(object sender, KeyboardTransitionEventArgs e)
        {
            tempmodel.Position += (e.T / 100.0f);
        }

        BaseModel tempmodel = null;
        void ViewScene_MouseRotated(object sender, MouseRotatedEventArgs e)
        {
            //throw new NotImplementedException();
            tempmodel.RotationMatrix *= e.RotationMatrix;
        }

        void cbbModel_ImageSelected(object sender, ImageSelectedEventArgs e)
        {
            viewControl.GetTarget().IsEnabled = false;
            //viewControl.SetTarget((BaseModel)cbbModel.SelectedItem);
            viewControl.GetTarget().IsEnabled = true;
        }

        void ObjectView_Loaded(object sender, RoutedEventArgs e)
        {
            IsLoaded = true;
            ExecuteScript("abc");
        }

        public bool ExecuteScript(string strScript)
        {
            if (IsLoaded == false)
                return false;
            ImportModel(new FileInfo(Utils.Global.StorePath + "/Scene/espilit/Models/" + "kit_face.ply"));
            ImportModel(new FileInfo(Utils.Global.StorePath + "/Scene/espilit/Models/" + "kit_face.ply"));
            return true;
        }

        public void AddModels(BaseModel[] models)
        {
            for (int i = 0; i < models.Length; i++)
            {
                AddModel(models[i]);
                models[i].IsEnabled = false;
            }
        }      

        private bool ImportModel(FileInfo file)
        {
            BaseModel model = BaseModel.Import(file);
            if (model == null)
                return false;

            if (tempmodel == null)
            {
                tempmodel = model;
            }
            //cbbModel.AddImage(model, new PathUri(_3DPresentation.Utils.Global.GetRandomSnapshot(), false));
            return AddModel(model);
        }

        public BaseModel GetTarget()
        {
            return viewControl.GetTarget();
        }

        public bool SetTarget(BaseModel model)
        {
            model.IsEnabled = true;
            return viewControl.SetTarget(model);
        }

        private bool AddModel(BaseModel model)
        {
            //cbbModel.AddImage(model, new PathUri(_3DPresentation.Utils.Global.GetRandomSnapshot(), false));
            return viewControl.AddModel(model);
        }

        private bool RemoveModel(BaseModel model)
        {
            return viewControl.RemoveModel(model);
        }

        public void ClearModels()
        {
            viewControl.ClearModels();
        }

        private void LayoutRoot_SizeChanged(object sender, SizeChangedEventArgs e)
        {
            //cbbModel.SetActualWidthAndHeight(LayoutRoot.ActualWidth, LayoutRoot.ActualHeight);
        }
    }
}
