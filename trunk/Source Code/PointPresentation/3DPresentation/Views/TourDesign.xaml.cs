using System;
using System.IO;
using System.Windows;
using System.Windows.Controls;
using _3DPresentation.Models;
using Microsoft.Xna.Framework;
using _3DPresentation.Views.Editor;

namespace _3DPresentation.Views
{
    public partial class TourDesign : UserControl
    {
        public bool IsLoaded { get; private set; }
        //public BaseModel SelectedModel { get; private set; }
        public TourDesign()
        {
            InitializeComponent();
            this.Loaded += new RoutedEventHandler(TourDesign_Loaded);
            this.KeyDown += new System.Windows.Input.KeyEventHandler(TourDesign_KeyDown);
            this.openFile.FileOpened += new OpenFileControl.FileOpenedHandler(openFile_FileOpened);
            this.cbModels.SelectionChanged += new SelectionChangedEventHandler(cbModels_SelectionChanged);
            cbbModel.SelectionChanged += new EventHandler(cbbModel_SelectionChanged);
        }

        void cbbModel_SelectionChanged(object sender, EventArgs e)
        {
            //throw new NotImplementedException();
            //SelectedModel = (BaseModel)cbModels.SelectedItem;
        }

        void TourDesign_KeyDown(object sender, System.Windows.Input.KeyEventArgs e)
        {
            if (tourControl.Target != null)
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
                moveDirection /= 10;
                tourControl.Target.Position += moveDirection;
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

        void TourDesign_Loaded(object sender, RoutedEventArgs e)
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
            ImportModel(new FileInfo(Utils.Global.StorePath + "/Scene/espilit/Models/" + "kit_face.ply"));
            ImportModel(new FileInfo(Utils.Global.StorePath + "/Scene/espilit/Models/" + "NotDecreaseSameVertex_0020.ply"));
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
                cbModels.Items.Add(model);
            return result;
        }

        private bool RemoveModel(BaseModel model)
        {
            bool result = tourControl.RemoveModel(model);
            if (result)
                cbModels.Items.Add(model);
            return result;
        }
    }
}
