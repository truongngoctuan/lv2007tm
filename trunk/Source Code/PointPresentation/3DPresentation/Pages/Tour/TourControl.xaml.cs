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
        public TourControl()
        {
            InitializeComponent();
            InitCustomScene();

            cbScene.Items.Add("wcafe.bsf");
            cbScene.Items.Add("espilit.bsf");

            babylonSurface.Loaded += new RoutedEventHandler(babylonSurface_Loaded);            
            this.SizeChanged += new SizeChangedEventHandler(TourControl_SizeChanged);            

            btLoadScene.Click += new RoutedEventHandler(btLoadScene_Click);
            myOpenFile.FileOpened += new OpenFileControl.FileOpenedHandler(myOpenFile_FileOpened);

            customScene.Drawed += new EventHandler(customScene_Drawed);

            cbModels.SelectionChanged += new SelectionChangedEventHandler(cbModels_SelectionChanged);
        }

        void cbModels_SelectionChanged(object sender, SelectionChangedEventArgs e)
        {
            customScene.GoToModel((FaceModel)cbModels.SelectedItem);
        }

        void customScene_Drawed(object sender, EventArgs e)
        {
            myCamPosition.Dispatcher.BeginInvoke(new Action(() => { myCamPosition.Text = "Camera Position: " + customScene.CameraPosition.X + " " + customScene.CameraPosition.Y + " " + customScene.CameraPosition.Z; }));
            myTargetPosition.Dispatcher.BeginInvoke(new Action(() => { myTargetPosition.Text = "Target Position: " + customScene.TargetPosition.X + " " + customScene.TargetPosition.Y + " " + customScene.TargetPosition.Z; }));
        }

        void myOpenFile_FileOpened(object sender, OpenFileControl.FileOpenedEventArgs e)
        {
            BaseModel model = customScene.AddModel(e.FileInfo);
            if(model != null)
                cbModels.Items.Add(model);
        }

        void InitCustomScene()
        {
            customScene = new CustomScene(this, babylonSurface, "CustomScene", babylonSurface.Engine);
            babylonSurface.SetCustomScene(customScene);
        }

        void babylonSurface_Loaded(object sender, RoutedEventArgs e)
        {
        }

        void btLoadScene_Click(object sender, RoutedEventArgs e)
        {
            if (cbScene.SelectedItem == null)
                return;
            LoadSceneLocal(cbScene.SelectedItem.ToString());
            //LoadScene("wcafe.bsf");
        }

        void TourControl_SizeChanged(object sender, SizeChangedEventArgs e)
        {
            babylonSurface.Engine.ResizeRenderZone((int)ActualWidth, (int)ActualHeight);
        }


        private void openButton_Click(object sender, RoutedEventArgs e)
        {
            //OpenFileDialog openFileDialog = new OpenFileDialog { Filter = Strings.OpenFileDialogFilter };

            //if (openFileDialog.ShowDialog() == true)
            //{
            //    using (FileStream stream = openFileDialog.File.OpenRead())
            //    {
            //        LoadScene(stream);
            //    }
            //}
        }

        private void LoadSceneLocal(string scene)
        {
            Uri sceneUri = Utils.Global.MakePackUri("Resources/Models/" + scene);
            babylonSurface.Scene.LoadLocal(sceneUri);
        }

        private void LoadScene(string scene)
        {
            Uri sceneUri = new Uri("http://www.catuhe.com/BSF/" + scene);
            babylonSurface.Scene.Load(sceneUri);
        }
    }
}
