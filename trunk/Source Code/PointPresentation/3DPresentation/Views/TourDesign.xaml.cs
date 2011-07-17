using System;
using System.IO;
using System.Windows;
using System.Windows.Controls;
using _3DPresentation.Models;
using Microsoft.Xna.Framework;
using _3DPresentation.Views.Editor;
using _3DPresentation.Data;

namespace _3DPresentation.Views
{
    public partial class TourDesign : UserControl
    {
        public bool IsLoaded { get; private set; }
        public BaseModel SelectedModel { get; private set; }
        private ObjectDesign objectDesign;
        public TourDesign()
        {
            InitializeComponent();
            objectDesign = new ObjectDesign();
            objectDesign.ParentView = this;

            this.Loaded += new RoutedEventHandler(TourDesign_Loaded);
            this.KeyDown += new System.Windows.Input.KeyEventHandler(TourDesign_KeyDown);

            this.openFile.FileOpened += new OpenFileControl.FileOpenedHandler(openFile_FileOpened);
            this.tourControl.SelectingModel += new EventHandler(tourControl_SelectingModel);
            
            this.cbbModel.ImageSelected += new ImageSelectedEventHandler(cbbModel_ImageSelected);
            btSave.Click += new RoutedEventHandler(btSave_Click);
        }

        void btSave_Click(object sender, RoutedEventArgs e)
        {
            tour.Models = tourControl.GetModels();
            tour.Save();
        }

        void cbbModel_ImageSelected(object sender, ImageSelectedEventArgs e)
        {
            SelectedModel = (BaseModel)e.SelectedItem;
        }

        void tourControl_SelectingModel(object sender, EventArgs e)
        {
            objectDesign.ClearModels();
            objectDesign.AddModels(tourControl.GetModels());
            objectDesign.SetTarget(tourControl.Target);
            objectDesign.ParentView = this;
            App.GoToPage(objectDesign);
        }        

        void TourDesign_KeyDown(object sender, System.Windows.Input.KeyEventArgs e)
        {
            if (SelectedModel != null)
            {       
                Vector3 moveDirection = Vector3.Zero;
                Matrix mat = Matrix.CreateFromYawPitchRoll(tourControl.Camera.RotationY, tourControl.Camera.RotationX, tourControl.Camera.RotationZ);
                if (e.Key == System.Windows.Input.Key.W)
                {
                    moveDirection = MathUtil.TransformPoint(mat, Vector3.Up);
                }
                else if (e.Key == System.Windows.Input.Key.S)
                {
                    moveDirection = MathUtil.TransformPoint(mat, Vector3.Down);
                }
                else if (e.Key == System.Windows.Input.Key.A)
                {
                    moveDirection = MathUtil.TransformPoint(mat, Vector3.Left);
                }
                else if (e.Key == System.Windows.Input.Key.D)
                {
                    moveDirection = MathUtil.TransformPoint(mat, Vector3.Right);
                }
                else if (e.Key == System.Windows.Input.Key.Q)
                {
                    moveDirection = MathUtil.TransformPoint(mat, Vector3.Backward);
                }
                else if (e.Key == System.Windows.Input.Key.E)
                {
                    moveDirection = MathUtil.TransformPoint(mat, Vector3.Forward);
                }
                else if (e.Key == System.Windows.Input.Key.Z)
                {
                    Babylon.Scene.bStandardModel = !Babylon.Scene.bStandardModel;
                }
                else if (e.Key == System.Windows.Input.Key.X)
                {
                    Babylon.Scene.bOpacityModel = !Babylon.Scene.bOpacityModel;
                }
                else if (e.Key == System.Windows.Input.Key.C)
                {
                    Babylon.Scene.bAlphaModel = !Babylon.Scene.bAlphaModel;
                }

                moveDirection /= 10;
                SelectedModel.Position += moveDirection;
            }
        }

        void cbModels_SelectionChanged(object sender, SelectionChangedEventArgs e)
        {
            //SelectedModel = (BaseModel)cbModels.SelectedItem;
        }

        void openFile_FileOpened(object sender, OpenFileControl.FileOpenedEventArgs e)
        {
            ImportModel(e.FileInfo);
        }


        Tour tour;
        void TourDesign_Loaded(object sender, RoutedEventArgs e)
        {
            IsLoaded = true;
            tour = Tour.Load("FirstTour");
            if (tour == null)
            {
                tour = new Tour();
                tour.Name = "FirstTour";
                tour.SceneName = "espilit";
                LoadSceneLocal(tour.SceneName);
                //ExecuteScript("abc");
            }
            else
            {
                LoadSceneLocal(tour.SceneName);
                for (int i = 0; i < tour.Models.Length; i++)
                    AddModel(tour.Models[i]);
            }
        }

        public bool ExecuteScript(string strScript)
        {
            if (IsLoaded == false)
                return false;

            LoadSceneLocal("espilit");
            //BaseModel model = BaseModel.Import(new FileInfo(Utils.Global.StorePath + "/Scene/espilit/Models/" + "kit_face.ply"));
            //model.Scale = 3.0f;
            //AddModel(model);
            //BaseModel model = BaseModel.Import(new FileInfo(Utils.Global.StorePath + "/Scene/espilit/Models/" + "horse_text.ply"));
            //model.Name = "horse_text";
            //model.Scale = 10.0f;
            //model.Position = new Vector3(0, 1, 0);
            //AddModel(model);
            BaseModel model = BaseModel.Import(new FileInfo(Utils.Global.StorePath + "/Scene/espilit/Models/" + "bunny_text.ply"));
            model.Name = "bunny_text";
            model.Scale = 10.0f;
            model.Position = new Vector3(0, 1, 3);
            AddModel(model);

            model = BaseModel.Import(new FileInfo(Utils.Global.StorePath + "/Scene/espilit/Models/" + "bunny_text.ply"));
            model.Name = "bunny_text2";
            model.Scale = 10.0f;
            model.Position = new Vector3(0, 2, 3);
            AddModel(model);

            model = BaseModel.Import(new FileInfo(Utils.Global.StorePath + "/Scene/espilit/Models/" + "Venus.ply"));
            model.Name = "Venus";
            model.Scale = 1.0f / 600.0f;
            model.Position = new Vector3(0, 1, 0);
            AddModel(model);

            model = BaseModel.Import(new FileInfo(Utils.Global.StorePath + "/Scene/espilit/Models/" + "monster.ply"));
            model.Name = "monster";
            model.Scale = 1.0f;
            model.Position = new Vector3(3, 1, 3);
            AddModel(model);

            //model = BaseModel.Import(new FileInfo(Utils.Global.StorePath + "/Scene/espilit/Models/" + "lucy_text.ply"));
            //model.Scale = 0.001f;
            //model.Position = new Vector3(0, 1, 6);
            //AddModel(model);
            //model = BaseModel.Import(new FileInfo(Utils.Global.StorePath + "/Scene/espilit/Models/" + "lion_text.ply"));
            //model.Scale = 10.0f;
            //model.Position = new Vector3(-3, 1, 6);
            //AddModel(model);
            //model = BaseModel.Import(new FileInfo(Utils.Global.StorePath + "/Scene/espilit/Models/" + "heptoroid_text.ply"));
            //model.Scale = 0.1f;
            //model.Position = new Vector3(-6, 1, 6);
            //AddModel(model);
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
            bool result = tourControl.AddModel(model);
            if (result)
                cbbModel.AddImage(model, model.toBitmap());
            return result;
        }

        private bool RemoveModel(BaseModel model)
        {
            bool result = tourControl.RemoveModel(model);
            return result;
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
