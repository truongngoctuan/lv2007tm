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
        public ObjectView()
        {
            InitializeComponent();
            this.Loaded += new RoutedEventHandler(ObjectView_Loaded);
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
            return true;
        }

        private bool ImportModel(FileInfo file)
        {
            BaseModel model = BaseModel.Import(file);
            if (model == null)
                return false;

            cbbModel.AddImage(model, new PathUri(_3DPresentation.Utils.Global.GetRandomSnapshot(), false));
            return AddModel(model);
        }

        private BaseModel GetTarget()
        {
            return viewControl.GetTarget();
        }

        private bool SetTarget(BaseModel model)
        {
            return viewControl.SetTarget(model);
        }

        private bool AddModel(BaseModel model)
        {
            return viewControl.AddModel(model);
        }

        private bool RemoveModel(BaseModel model)
        {
            return viewControl.RemoveModel(model);
        }

        private void ClearModels()
        {
            viewControl.ClearModels();
        }

        private void LayoutRoot_SizeChanged(object sender, SizeChangedEventArgs e)
        {
            cbbModel.SetActualWidthAndHeight(LayoutRoot.ActualWidth, LayoutRoot.ActualHeight);
        }
    }
}
