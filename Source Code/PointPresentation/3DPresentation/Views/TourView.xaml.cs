using System;
using System.IO;
using System.Windows;
using System.Windows.Controls;
using _3DPresentation.Models;
using _3DPresentation.Views.Editor;

namespace _3DPresentation.Views
{
    public partial class TourView : UserControl
    {
        public bool IsLoaded { get; private set; }
        public TourView()
        {            
            InitializeComponent();
            this.Loaded += new RoutedEventHandler(TourView_Loaded);
        }

        void TourView_Loaded(object sender, RoutedEventArgs e)
        {
            IsLoaded = true;
            ExecuteScript("abc");
        }

        public bool ExecuteScript(string strScript)
        {
            if (IsLoaded == false)
                return false;
            LoadSceneLocal("espilit");
            ImportModel(new FileInfo(Utils.Global.StorePath + "/Scene/espilit/Models/" + "kit_face.ply"));
            
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
            cbbModel.AddImage(model, new PathUri(_3DPresentation.Utils.Global.GetRandomSnapshot(), false));
            return tourControl.AddModel(model);
        }

        private bool RemoveModel(BaseModel model)
        {
            return tourControl.RemoveModel(model);
        }
    }
}
