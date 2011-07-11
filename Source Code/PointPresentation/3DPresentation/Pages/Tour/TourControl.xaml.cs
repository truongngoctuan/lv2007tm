﻿using System;
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

            myCamPosition.Visibility = System.Windows.Visibility.Collapsed;
            myTargetPosition.Visibility = System.Windows.Visibility.Collapsed;
            cbScene.Visibility = System.Windows.Visibility.Collapsed;
            cbModels.Visibility = System.Windows.Visibility.Collapsed;
            btLoadScene.Visibility = System.Windows.Visibility.Collapsed;
            myOpenFile.Visibility = System.Windows.Visibility.Collapsed;

            btLoadScene.Click += new RoutedEventHandler(btLoadScene_Click);
            myOpenFile.FileOpened += new OpenFileControl.FileOpenedHandler(myOpenFile_FileOpened);

            cbModels.SelectionChanged += new SelectionChangedEventHandler(cbModels_SelectionChanged);
            cbScene.Items.Add("wcafe.bsf");
            cbScene.Items.Add("espilit.bsf");
        }

        void TourControl_Loaded(object sender, RoutedEventArgs e)
        {
            
        }

        void InitCustomScene()
        {
            customScene = new CustomScene(this, babylonSurface, "CustomScene", babylonSurface.Engine);
            babylonSurface.SetCustomScene(customScene);

            customScene.Drawed += new EventHandler(customScene_Drawed);
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

        void cbModels_SelectionChanged(object sender, SelectionChangedEventArgs e)
        {
            customScene.GoToModel((BaseModel)cbModels.SelectedItem);
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

        void customScene_Drawed(object sender, EventArgs e)
        {
            //if(myCamPosition.Visibility == System.Windows.Visibility.Visible)
                myCamPosition.Dispatcher.BeginInvoke(new Action(() => { myCamPosition.Text = "Camera Position: " + customScene.CameraPosition.X + " " + customScene.CameraPosition.Y + " " + customScene.CameraPosition.Z; }));
            //if (myTargetPosition.Visibility == System.Windows.Visibility.Visible)
                myTargetPosition.Dispatcher.BeginInvoke(new Action(() => { myTargetPosition.Text = "Target Position: " + customScene.TargetPosition.X + " " + customScene.TargetPosition.Y + " " + customScene.TargetPosition.Z; }));
        }

        void myOpenFile_FileOpened(object sender, OpenFileControl.FileOpenedEventArgs e)
        {
            //BaseModel model = customScene.AddModel(e.FileInfo);
            //if(model != null)
            //    cbModels.Items.Add(model);
        }        

        void btLoadScene_Click(object sender, RoutedEventArgs e)
        {
            if (cbScene.SelectedItem == null)
                return;
            Uri sceneUri = Utils.Global.MakeStoreUri(string.Format("Scene/{0}/{0}.bsf", "espilit"));
            //LoadSceneLocal(sceneUri);
            LoadSceneInPackage(cbScene.SelectedItem.ToString());
            //LoadScene("wcafe.bsf");
        }        
    }
}
