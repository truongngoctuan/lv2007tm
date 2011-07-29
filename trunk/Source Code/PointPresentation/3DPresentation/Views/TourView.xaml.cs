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
        private static ObjectView objectView;
        private static TourControl tourControl;
        public TourView()
        {            
            InitializeComponent();
            tourControl = new TourControl();
            tourControl.SelectingModel += new EventHandler(tourControl_SelectingModel);            
            this.DrawingRoot.Children.Add(tourControl);

            objectView = new ObjectView();
            objectView.ParentView = this;

            cbbModel.ImageSelected += new ImageSelectedEventHandler(cbbModel_ImageSelected);

            this.Loaded += new RoutedEventHandler(TourView_Loaded);
        }

        void cbbModel_ImageSelected(object sender, ImageSelectedEventArgs e)
        {
            
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
                LoadSceneInPackage(CurrentTour.SceneName);
                for (int i = 0; i < CurrentTour.Models.Length; i++)
                    AddModel(CurrentTour.Models[i]);
            }
        }

        public string TourName { get; set; }
        private Tour CurrentTour { get; set; }
        void TourView_Loaded(object sender, RoutedEventArgs e)
        {
            IsLoaded = true;
            if (CurrentTour == null)
                LoadTour(TourName);
        }

        private void LoadScene(string scene)
        {
            Uri sceneUri = new Uri("http://www.catuhe.com/BSF/" + scene);
            tourControl.LoadScene(sceneUri);
        }

        private void LoadSceneInPackage(string scene)
        {
            Uri sceneUri = Utils.Global.MakePackUri(string.Format("Resources/Models/{0}.bsf", scene));
            tourControl.LoadSceneInPackage(sceneUri);
        }

        //private void LoadSceneLocal(string scene)
        //{
        //    Uri sceneUri = Utils.Global.MakeStoreUri(string.Format("Scene/{0}/{0}.bsf", scene));
        //    tourControl.LoadSceneLocal(sceneUri);
        //}        

        private bool AddModel(BaseModel model)
        {
            bool result = tourControl.AddModel(model);
            if (result)
                cbbModel.AddImage(model, model.toBitmap());

            return result;
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
            App.GoToPage(this.ParentView);
        }
    }
}
