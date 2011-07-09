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
using _3DPresentation.Models;

namespace _3DPresentation.Views.Editor
{
    public partial class cwMatchModelManual : ChildWindow
    {
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

        public cwMatchModelManual()
        {
            InitializeComponent();

            //RotateX.setParams(this, "rx", "Rotate X: ", -180, 180, 0);
            //RotateY.setParams(this, "ry", "Rotate Y: ", -180, 180, 0);
            //RotateZ.setParams(this, "rz", "Rotate Z: ", -180, 180, 0);

            //TransateX.setParams(this, "tx", "Translate X: ", -500, 500, 0);
            //TransateY.setParams(this, "ty", "Translate Y: ", -500, 500, 0);
            //TransateZ.setParams(this, "tz", "Translate Z: ", -500, 500, 0);

            //ScaleX.setParams(this, "sx", "Scale X: ", -10, 10, 1);
            //ScaleY.setParams(this, "sy", "Scale Y: ", -10, 10, 1);
            //ScaleZ.setParams(this, "sz", "Scale Z: ", -10, 10, 1);

            tblockValue.Text = this.ToString();
            this.Effect = null;
        }

        private void OKButton_Click(object sender, RoutedEventArgs e)
        {
            this.DialogResult = true;
        }

        private void CancelButton_Click(object sender, RoutedEventArgs e)
        {
            this.DialogResult = false;
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
                        break;
                    }
                case "ry":
                    {
                        _fRotateY = fValue;
                        break;
                    }
                case "rz":
                    {
                        _fRotateZ = fValue;
                        break;
                    }
                case "tx":
                    {
                        _fTranslateX = fValue;
                        break;
                    }
                case "ty":
                    {
                        _fTranslateY = fValue;
                        break;
                    }
                case "tz":
                    {
                        _fTranslateZ = fValue;
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
            vcOjectViewer.AddModel(newModel1);
            //vcOjectViewer.AddModel(_model2);
            vcOjectViewer.SetTarget(newModel1);

            tblockValue.Text = this.ToString();
        }

    }
}

