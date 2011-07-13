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
using System.IO;
using Microsoft.Xna.Framework;
using _3DPresentation.Models;

namespace _3DPresentation
{
    public partial class TourControl : UserControl
    {
        CustomScene customScene;
        public event EventHandler SelectingModel;
        public float FPS
        {
            get { return customScene.FPS; }
        }
        public Babylon.Camera Camera
        {
            get { return customScene.ActiveCamera; }
        }
        public BaseModel Target
        {
            get { return customScene.Target; }
        }
        public bool IsSceneLoaded { get; private set; }
        public TourControl()
        {
            InitializeComponent();
            InitCustomScene();

            this.Loaded += new RoutedEventHandler(TourControl_Loaded);
            this.SizeChanged += new SizeChangedEventHandler(TourControl_SizeChanged);
        }

        void TourControl_Loaded(object sender, RoutedEventArgs e)
        {
            
        }

        void InitCustomScene()
        {
            customScene = new CustomScene(this, babylonSurface, "CustomScene", babylonSurface.Engine);
            babylonSurface.SetCustomScene(customScene);

            customScene.SelectingModel += new EventHandler(customScene_SelectingModel);
            babylonSurface.Loaded += new RoutedEventHandler(babylonSurface_Loaded);
        }

        void customScene_SelectingModel(object sender, EventArgs e)
        {
            if (SelectingModel != null)
                SelectingModel(this, EventArgs.Empty);
        }

        void babylonSurface_Loaded(object sender, RoutedEventArgs e)
        {
        }

        void TourControl_SizeChanged(object sender, SizeChangedEventArgs e)
        {
            babylonSurface.Engine.ResizeRenderZone((int)ActualWidth, (int)ActualHeight);
        }

        public void GoToModel(BaseModel model)
        {
            customScene.GoToModel(model);
        }

        public bool AddModel(BaseModel model)
        {
            return customScene.AddModel(model);
        }

        public bool RemoveModel(BaseModel model)
        {
            return customScene.RemoveModel(model);
        }

        public BaseModel[] GetModels()
        {
            return customScene.GetModels();
        }

        public void LoadSceneInPackage(Uri sceneUri)
        {
            babylonSurface.Scene.LoadPack(sceneUri);
        }

        public void LoadSceneLocal(Uri sceneUri)
        {
            babylonSurface.Scene.LoadLocal(sceneUri);
        }

        public void LoadScene(Uri sceneUri)
        {
            babylonSurface.Scene.Load(sceneUri);
        }

        public void LoadSceneInPackage(string scene)
        {
            Uri sceneUri = Utils.Global.MakePackUri("Resources/Models/" + scene);
            babylonSurface.Scene.LoadPack(sceneUri);
        }

        //public void LoadScene(string scene)
        //{
        //    Uri sceneUri = new Uri("http://www.catuhe.com/BSF/" + scene);
        //    babylonSurface.Scene.Load(sceneUri);
        //}    
    }
}
