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
using Microsoft.Xna.Framework;

namespace _3DPresentation.Views.Editor
{
    public partial class MatchModelManual : UserControl
    {
        //UserControl _parentView;

        //public UserControl ParentView
        //{
        //    get { return _parentView; }
        //    set { _parentView = value; }
        //}

        public MatchModelManual()
        {
            InitializeComponent();

            //tblockValue.Text = this.ToString();

            vcOjectViewer.IsTabStop = true;
            vcOjectViewer.Focus();
            tboxFactorRotation.IsTabStop = true;
            tboxFactorTransition.IsTabStop = true;

            vcOjectViewer.ViewScene.KeyboardTransition += new KeyboardTransitionEventHandler(ViewScene_KeyboardTransition);
            vcOjectViewer.ViewScene.MouseRotated += new MouseRotatedEventHandler(ViewScene_MouseRotated);

            tboxFactorRotation_TextChanged(this, null);
            tboxFactorTransition_TextChanged(this, null);

            vcOjectViewer.BackgoundColor = System.Windows.Media.Color.FromArgb(255, 0, 0, 0);
            colorPicker1.Color = vcOjectViewer.BackgoundColor;

            _deltaRotationMatrix = Microsoft.Xna.Framework.Matrix.Identity;
        }

        int iFixedImageIndex = -1;
        int iReferenceImageIndex = -1;

        BaseModel _model1 = null;
        BaseModel _model2 = null;

        //Vector3 v3OldRotation;
        Vector3 v3OldPosition;
        Microsoft.Xna.Framework.Matrix OldRotationMatrix;

        Vector3 v3DeltaPosition = Vector3.Zero;
        Microsoft.Xna.Framework.Matrix _deltaRotationMatrix = Microsoft.Xna.Framework.Matrix.Identity;


        void ResetModel()
        {
            //_model2.Rotation = v3OldRotation;
            _model2.RotationMatrix = OldRotationMatrix;
            _model2.Position = v3OldPosition;
        }
        public event EventHandler OKButtonClick;
        public event EventHandler CancelButtonClick;
        private void OKButton_Click(object sender, RoutedEventArgs e)
        {
            Result = true;
            //update cho parentview
            vcOjectViewer.RemoveModel(_model2);
            vcOjectViewer.RemoveModel(_model1);
            App.RemovePage(this);

            if (MatchManualFinished != null)
            {
                TranslationRotationEventArgs eArg = new TranslationRotationEventArgs();
                eArg.RotationMatrix = _deltaRotationMatrix;
                eArg.TransitionMatrix = v3DeltaPosition;
                eArg.ReferenceIndex = iReferenceImageIndex;
                eArg.ApplyToAllFrameAfter = (bool)cboxApplyToAllFrameAfter.IsChecked;
                if (iFixedImageIndex < iReferenceImageIndex)
                {
                    eArg.IsAfter = true;
                }
                else
                {
                    eArg.IsAfter = false;
                }


                ResetModel();
                MatchManualFinished(this, eArg);
            }
            //App.GoToPage(ParentView);

            if (OKButtonClick != null)
            {
                OKButtonClick(this, null);
            }
        }

        private void CancelButton_Click(object sender, RoutedEventArgs e)
        {
            Result = false;
            vcOjectViewer.RemoveModel(_model2);
            vcOjectViewer.RemoveModel(_model1);

            ResetModel();

            //App.RemovePage(this);
            //App.GoToPage(ParentView);

            if (CancelButtonClick != null)
            {
                CancelButtonClick(this, null);
            }
        }

        #region ValueChange
        public void Change()
        {
            //tblockUpdateCounter.Text = (int.Parse(tblockUpdateCounter.Text) + 1).ToString();
        }

        private void tboxFactorRotation_TextChanged(object sender, TextChangedEventArgs e)
        {
            float iResult = 0;
            if (float.TryParse(tboxFactorRotation.Text, out iResult))
            {
                vcOjectViewer.ViewScene.FactorRotation = iResult;
            }
        }

        private void tboxFactorTransition_TextChanged(object sender, TextChangedEventArgs e)
        {
            float iResult = 0;
            if (float.TryParse(tboxFactorTransition.Text, out iResult))
            {
                vcOjectViewer.ViewScene.FactorTransition = iResult;
            }
        }

        void ViewScene_MouseRotated(object sender, MouseRotatedEventArgs e)
        {
            if (e.IsFinished)
            {
                _deltaRotationMatrix *= (e.DeltaRotationMatrix);
                _model2.RotationMatrix = OldRotationMatrix * _deltaRotationMatrix;
                Change();
            }
            else
            {
                //DeltaRotationMatrix *= (e.DeltaRotationMatrix);
                _model2.RotationMatrix = OldRotationMatrix * _deltaRotationMatrix * e.DeltaRotationMatrix;
                Change();
            }
            
        }

        void ViewScene_KeyboardTransition(object sender, KeyboardTransitionEventArgs e)
        {
            v3DeltaPosition += e.T;
            _model2.Position = v3OldPosition + v3DeltaPosition;
            Change();
        }

        #endregion
        public override string ToString()
        {
            return string.Format("index1: {0}\nindex2: {1}\n", iFixedImageIndex, iReferenceImageIndex);
        }

        #region in - outdata
        public void SetInputData(int iFFIndex, int iRIndex)
        {
            iFixedImageIndex = iFFIndex;
            iReferenceImageIndex = iRIndex;

            //tblockValue.Text = this.ToString();
        }

        public void SetInputData(BaseModel model1, BaseModel model2)
        {
            _model1 = model1;
            _model2 = model2;

            vcOjectViewer.AddModel(_model1);
            vcOjectViewer.AddModel(_model2);
            vcOjectViewer.SetTarget(_model2);

            //tblockValue.Text = this.ToString();

            //luu lai
            //v3OldRotation = _model2.Rotation;
            v3OldPosition = _model2.Position;
            OldRotationMatrix = _model2.RotationMatrix;
            _deltaRotationMatrix = Microsoft.Xna.Framework.Matrix.Identity;
        }
        #endregion

        bool _bResult;

        public bool Result
        {
            get { return _bResult; }
            set { _bResult = value; }
        }
        #region New in - out
        public event TranslationRotationEventHandler MatchManualFinished;

        public class TranslationRotationEventArgs : EventArgs
        {
            public Microsoft.Xna.Framework.Matrix RotationMatrix;
            public Vector3 TransitionMatrix;
            public int ReferenceIndex;
            public bool ApplyToAllFrameAfter;
            public bool IsAfter;
        }

        public delegate void TranslationRotationEventHandler(object sender, TranslationRotationEventArgs e);
        #endregion

        private void rotationCanvas_MouseLeftButtonDown(object sender, MouseButtonEventArgs e)
        {
            tboxFactorRotation.Focus();
        }

        private void transitionCanvas_MouseLeftButtonDown(object sender, MouseButtonEventArgs e)
        {
            tboxFactorTransition.Focus();
        }

        private void colorPicker1_ColorChanged(object sender, System.ComponentModel.PropertyChangedEventArgs e)
        {
            if (colorPicker1 != null)
            {
                //MessageBox.Show(colorPicker1.Color.ToString());
                //(ellipse00.Fill as SolidColorBrush).Color = colorPicker1.Color;
                vcOjectViewer.BackgoundColor = colorPicker1.Color;
            }
        }
    }
}
