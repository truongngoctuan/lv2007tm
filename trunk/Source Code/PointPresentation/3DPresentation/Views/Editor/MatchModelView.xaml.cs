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
using System.Windows.Navigation;
using _3DPresentation.Models;
using Microsoft.Xna.Framework;

namespace _3DPresentation.Views.Editor
{
    public partial class MatchModelView : Page
    {
        UserControl _parentView;

        public UserControl ParentView
        {
            get { return _parentView; }
            set { _parentView = value; }
        }

        public MatchModelView()
        {
            InitializeComponent();

            RotateX.setParams(this, "rx", "Rotate X: ", -180, 180, 0);
            RotateY.setParams(this, "ry", "Rotate Y: ", -180, 180, 0);
            RotateZ.setParams(this, "rz", "Rotate Z: ", -180, 180, 0);

            TransateX.setParams(this, "tx", "Translate X: ", -500, 500, 0);
            TransateY.setParams(this, "ty", "Translate Y: ", -500, 500, 0);
            TransateZ.setParams(this, "tz", "Translate Z: ", -500, 500, 0);

            ScaleX.setParams(this, "sx", "Scale X: ", -10, 10, 1);
            ScaleY.setParams(this, "sy", "Scale Y: ", -10, 10, 1);
            ScaleZ.setParams(this, "sz", "Scale Z: ", -10, 10, 1);

            tblockValue.Text = this.ToString();
            this.Effect = null;
        }

        // Executes when the user navigates to this page.
        protected override void OnNavigatedTo(NavigationEventArgs e)
        {
        }
                
        float _fRotateX = 0;
        float _fRotateY = 0;
        float _fRotateZ = 0;
        float _fTranslateX = 0;
        float _fTranslateY = 0;
        float _fTranslateZ = 0;
        float _fScaleX = 1;
        float _fScaleY = 1;
        float _fScaleZ = 1;

        int iFixedImageIndex = -1;
        int iReferenceImageIndex = -1;

        BaseModel _model1 = null;
        BaseModel _model2 = null;

        Vector3 v3OldRotation;
        Vector3 v3OldPosition;

        void ResetModel()
        {
            _model2.Rotation = v3OldRotation;
            _model2.Position = v3OldPosition;
        }

        private void OKButton_Click(object sender, RoutedEventArgs e)
        {
            Result = true;
            //update cho parentview
            vcOjectViewer.RemoveModel(_model2);
            vcOjectViewer.RemoveModel(_model1);
            App.RemovePage(this);

            ResetModel();

            ((EditorView)ParentView).UpdateMatrixAfterFrame(iReferenceImageIndex, 
                new Vector3(_fRotateX * 3.14f / 180.0f, _fRotateY * 3.14f / 180.0f, _fRotateZ * 3.14f / 180.0f),
                new Vector3(_fTranslateX, _fTranslateY, _fTranslateZ));

            App.GoToPage(ParentView);
        }

        private void CancelButton_Click(object sender, RoutedEventArgs e)
        {
            Result = false;
            vcOjectViewer.RemoveModel(_model2);
            vcOjectViewer.RemoveModel(_model1);
            App.RemovePage(this);
            App.GoToPage(ParentView);
        }

        #region ValueChange
        public void Change()
        {
            tblockUpdateCounter.Text = (int.Parse(tblockUpdateCounter.Text) + 1).ToString();
        }
        public void OnValueChange(string strKey, float fValue)
        {
            if (!(bool)cbPreview.IsChecked) return;
            switch (strKey)
            {
                case "rx":
                    {
                        _fRotateX = fValue;
                        UpdateModelRotate();
                        break;
                    }
                case "ry":
                    {
                        _fRotateY = fValue;
                        UpdateModelRotate();
                        break;
                    }
                case "rz":
                    {
                        _fRotateZ = fValue;
                        UpdateModelRotate();
                        break;
                    }
                case "tx":
                    {
                        _fTranslateX = fValue;
                        UpdateModelTranslate();
                        break;
                    }
                case "ty":
                    {
                        _fTranslateY = fValue;
                        UpdateModelTranslate();
                        break;
                    }
                case "tz":
                    {
                        _fTranslateZ = fValue;
                        UpdateModelTranslate();
                        break;
                    }
                case "sx":
                    {
                        _fScaleX = fValue;
                        break;
                    }
                case "sy":
                    {
                        _fScaleY = fValue;
                        break;
                    }
                case "sz":
                    {
                        _fScaleZ = fValue;
                        break;
                    }
            }

            tblockValue.Text = this.ToString();
        }

        public void UpdateModelRotate()
        {
            _model2.Rotation = new Microsoft.Xna.Framework.Vector3(_fRotateX * 3.14f / 180.0f, _fRotateY * 3.14f / 180.0f, _fRotateZ * 3.14f / 180.0f);
        }
        public void UpdateModelTranslate()
        {
            _model2.Position = new Microsoft.Xna.Framework.Vector3(_fTranslateX, _fTranslateY, _fTranslateZ);
        }
        #endregion
        public override string ToString()
        {
            //return base.ToString();
            return string.Format("index1: {9}\nindex2: {10}\n{0} {1} {2}\n{3} {4} {5}\n{6} {7} {8}",
                _fRotateX, _fRotateY, _fRotateZ, _fTranslateX, _fTranslateY, _fTranslateZ, _fScaleX, _fScaleY, _fScaleZ,
                iFixedImageIndex, iReferenceImageIndex);
        }

        private void cbPreview_Checked(object sender, RoutedEventArgs e)
        {
            if (cbPreview != null && (bool)cbPreview.IsChecked)
            {
                //update all data
                _fRotateX = RotateX.Value;
                _fRotateY = RotateX.Value;
                _fRotateZ = RotateX.Value;
                _fTranslateX = TransateX.Value;
                _fTranslateY = TransateY.Value;
                _fTranslateZ = TransateZ.Value;
                _fScaleX = ScaleX.Value;
                _fScaleY = ScaleY.Value;
                _fScaleZ = ScaleZ.Value;

                tblockValue.Text = this.ToString();
            }
        }

        #region in - outdata
        public void SetInputData(int iFFIndex, int iRIndex)
        {
            iFixedImageIndex = iFFIndex;
            iReferenceImageIndex = iRIndex;

            tblockValue.Text = this.ToString();
        }

        public void SetInputData(BaseModel model1, BaseModel model2)
        {
            _model1 = model1;
            _model2 = model2;

            BaseModel newModel1 = PointModel.Import(new System.IO.FileInfo("d:\\NotDecreaseSameVertex_0000.ply"));
            vcOjectViewer.AddModel(model1);
            vcOjectViewer.AddModel(_model2);
            vcOjectViewer.SetTarget(model1);

            tblockValue.Text = this.ToString();

            //luu lai
            v3OldRotation = _model2.Rotation;
            v3OldPosition = _model2.Position;

            //dong bo hoa voi cac bien trong page
            _fRotateX = _model2.Rotation.X;
            _fRotateY = _model2.Rotation.Y;
            _fRotateZ = _model2.Rotation.Z;

            _fTranslateX = _model2.Position.X;
            _fTranslateY = _model2.Position.Y;
            _fTranslateZ = _model2.Position.Z;
        }

        public Vector3 Rotate1
        {
            get { return new Vector3(0, 0, 0); }
        }

        public Vector3 Translate1
        {
            get { return new Vector3(0, 0, 0); }
        }

        public Vector3 Rotate2
        {
            get { return new Vector3(_fRotateX, _fRotateY, _fRotateZ); }
        }

        public Vector3 Translate2
        {
            get { return new Vector3(_fTranslateX, _fTranslateY, _fTranslateZ); }
        }

        #endregion

        bool _bResult;

        public bool Result
        {
            get { return _bResult; }
            set { _bResult = value; }
        }
    }
}
