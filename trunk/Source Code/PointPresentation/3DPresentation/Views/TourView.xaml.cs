using System;
using System.IO;
using System.Windows;
using System.Windows.Controls;
using _3DPresentation.Models;
using _3DPresentation.Views.Editor;
using Microsoft.Xna.Framework;
using _3DPresentation.Data;

namespace _3DPresentation.Views
{
    public partial class TourView : UserControl
    {
        public bool IsLoaded { get; private set; }
        private ObjectView objectView;
        public TourView()
        {            
            InitializeComponent();
            objectView = new ObjectView();
            objectView.ParentView = this;

            cbbModel.ImageSelected += new ImageSelectedEventHandler(cbbModel_ImageSelected);

            this.Loaded += new RoutedEventHandler(TourView_Loaded);
            this.tourControl.SelectingModel += new EventHandler(tourControl_SelectingModel);            
        }

        void cbbModel_ImageSelected(object sender, ImageSelectedEventArgs e)
        {
            //throw new NotImplementedException();
            //objectView.ClearModels();
            //objectView.AddModels(tourControl.GetModels());
            //objectView.SetTarget((BaseModel)e.SelectedItem);
            //objectView.ParentView = this;
            //App.GoToPage(objectView);
        }

        void tourControl_SelectingModel(object sender, EventArgs e)
        {
            objectView.ClearModels();
            objectView.AddModels(tourControl.GetModels());
            objectView.SetTarget(tourControl.Target);
            objectView.ParentView = this;
            App.RemovePage(this);
            App.GoToPage(objectView);
        }

        public void LoadTour(string strTourName)
        {
            if (strTourName == null || strTourName.Length == 0)
                return;
            CurrentTour = Tour.Load(strTourName);
            if (CurrentTour != null)
            {
                LoadSceneLocal(CurrentTour.SceneName);
                for (int i = 0; i < CurrentTour.Models.Length; i++)
                    AddModel(CurrentTour.Models[i]);
            }
        }

        public string TourName { get; set; }
        private Tour CurrentTour { get; set; }
        void TourView_Loaded(object sender, RoutedEventArgs e)
        {
            IsLoaded = true;
            LoadTour(TourName);
            //ExecuteScript("abc");

            //MessageBox.Show(LayoutRoot.Width.ToString() + " " + LayoutRoot.ActualWidth.ToString());            
        }

        public bool ExecuteScript(string strScript)
        {
            if (IsLoaded == false)
                return false;
            LoadSceneLocal("espilit");
            //ImportModel(new FileInfo(Utils.Global.StorePath + "/Scene/espilit/Models/" + "kit_face.ply"));
            BaseModel model = BaseModel.Import(new FileInfo(Utils.Global.StorePath + "/Scene/espilit/Models/" + "bunny_text.ply"));
            model.Scale = 10.0f;
            model.Position = new Vector3(0, 1, 0);
            AddModel(model);
            model = BaseModel.Import(new FileInfo(Utils.Global.StorePath + "/Scene/espilit/Models/" + "kit_face.ply"));
            model.Scale = 10.0f;
            model.Position = new Vector3(0, 2, 3);
            AddModel(model);
            model = BaseModel.Import(new FileInfo(Utils.Global.StorePath + "/Scene/espilit/Models/" + "bunny_text.ply"));
            model.Scale = 0.001f;
            model.Position = new Vector3(0, 1, 6);
            AddModel(model);
            return true;
        }

        private bool ImportModel(FileInfo file)
        {
            BaseModel model = BaseModel.Import(file);
            if (model == null)
                return false;
            return AddModel(model);
        }

        private void LoadScene(string scene)
        {
            Uri sceneUri = new Uri("http://www.catuhe.com/BSF/" + scene);
            tourControl.LoadScene(sceneUri);
        }

        private void LoadSceneInPackage(string scene)
        {
            Uri sceneUri = Utils.Global.MakePackUri(string.Format("Resources/Models/{0}.bsf", scene));
            tourControl.LoadSceneLocal(sceneUri);
        }

        private void LoadSceneLocal(string scene)
        {
            Uri sceneUri = Utils.Global.MakeStoreUri(string.Format("Scene/{0}/{0}.bsf", scene));
            tourControl.LoadSceneLocal(sceneUri);
        }        

        private bool AddModel(BaseModel model)
        {
            cbbModel.AddImage(model, model.toBitmap());
            return tourControl.AddModel(model);
        }

        private bool RemoveModel(BaseModel model)
        {
            return tourControl.RemoveModel(model);
        }

        private void LayoutRoot_SizeChanged(object sender, SizeChangedEventArgs e)
        {
            cbbModel.SetActualWidthAndHeight(LayoutRoot.ActualWidth, LayoutRoot.ActualHeight);
        }

        UserControl _parentView = null;

        public UserControl ParentView
        {
            get { return _parentView; }
            set { _parentView = value; }
        }
        private void btBack_Click(object sender, RoutedEventArgs e)
        {
            App.RemovePage(this);
            App.GoToPage(ParentView);
        }
    }
}
