﻿using System;
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
            this.KeyUp += new System.Windows.Input.KeyEventHandler(TourDesign_KeyUp);
            this.MouseLeftButtonDown += new System.Windows.Input.MouseButtonEventHandler(Container_MouseLeftButtonDown);
            this.MouseLeftButtonUp += new System.Windows.Input.MouseButtonEventHandler(Container_MouseLeftButtonUp);
            this.MouseMove += new System.Windows.Input.MouseEventHandler(Container_MouseMove);

            this.tourControl.SelectingModel += new EventHandler(tourControl_SelectingModel);
            
            this.cbbModel.ImageSelected += new ImageSelectedEventHandler(cbbModel_ImageSelected);
            btSave.Click += new RoutedEventHandler(btSave_Click);
            btAddModel.Click += new RoutedEventHandler(btAddModel_Click);
            btRemoveModel.Click += new RoutedEventHandler(btRemoveModel_Click);
        }

        void btRemoveModel_Click(object sender, RoutedEventArgs e)
        {
            if (SelectedModel != null)
            {
                RemoveModel(SelectedModel);
                //cbbModel.DeleteImage(cbbModel.SelectedIndex);
            }
            SelectedModel = null;
        }

        void btAddModel_Click(object sender, RoutedEventArgs e)
        {
            OpenFileDialog dialog = new OpenFileDialog();
            dialog.Multiselect = false;
            dialog.Filter = "Model|*.ply|Text|*.txt|All Files|*.*";
            if (dialog.ShowDialog() == true)
            {
                ImportModel(dialog.File);
            }            
        }

        void btSave_Click(object sender, RoutedEventArgs e)
        {
            CurrentTour.Models = tourControl.GetModels();
            CurrentTour.Save();
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
        void TourDesign_KeyUp(object sender, System.Windows.Input.KeyEventArgs e)
        {
            if (e.Key == System.Windows.Input.Key.Ctrl)
            {
                CtrlKeyDown = false;
                bRotateModel = false;
            }
        }

        void TourDesign_KeyDown(object sender, System.Windows.Input.KeyEventArgs e)
        {
            if (SelectedModel != null)
            {
                if (e.Key == System.Windows.Input.Key.Ctrl)
                {
                    CtrlKeyDown = true;
                }


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
        void TourDesign_Loaded(object sender, RoutedEventArgs e)
        {
            IsLoaded = true;
            LoadTour(TourName);
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

        #region Rotate Model
        bool mouseLeftDown;
        bool CtrlKeyDown = false;
        bool bRotateModel = false;

        void Container_MouseLeftButtonUp(object sender, System.Windows.Input.MouseButtonEventArgs e)
        {
            mouseLeftDown = false;
            deltaRotationMatrix = Matrix.Identity;
            bRotateModel = false;
        }

        void Container_MouseLeftButtonDown(object sender, System.Windows.Input.MouseButtonEventArgs e)
        {
            //Container.Focus();
            mouseLeftDown = true;
            startPosition = lastPosition = e.GetPosition(this);

            if (CtrlKeyDown)
            {
                bRotateModel = true;
                //ChangeToRotationModelState();
            }
        }

        Point lastPosition;
        Point startPosition;
        Microsoft.Xna.Framework.Matrix deltaRotationMatrix = Microsoft.Xna.Framework.Matrix.Identity;
        void Container_MouseMove(object sender, System.Windows.Input.MouseEventArgs e)
        {
            if (bRotateModel)
            {
                Point currentPosition = e.GetPosition(this);
                if (!mouseLeftDown)
                    return;

                Microsoft.Xna.Framework.Matrix lastMat = toRotationMatrix(lastPosition, currentPosition);
                lastPosition = currentPosition;

                if (SelectedModel != null)
                {
                    SelectedModel.RotationMatrix *= lastMat;
                }
            }
        }


        private Microsoft.Xna.Framework.Matrix toRotationMatrix(Point LastPosition, Point currentPosition)
        {
            float dX, dY;
            dX = (float)(currentPosition.X - LastPosition.X) * 3.14f / 180.0f;
            dY = (float)(currentPosition.Y - LastPosition.Y) * 3.14f / 180.0f;

            Microsoft.Xna.Framework.Matrix lastMat = Matrix.CreateFromYawPitchRoll(dX,0, 0);
            return lastMat;
        }

        #endregion
    }
}
