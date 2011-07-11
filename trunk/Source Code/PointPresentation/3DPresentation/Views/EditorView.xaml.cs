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
using System.Windows.Navigation;
using System.Windows.Shapes;
using _3DPresentation.Views.Editor;
using System.Windows.Controls.Primitives;
using System.Threading;
using _3DPresentation.Models;
using System.Windows.Media.Imaging;
using Microsoft.Xna.Framework;
using System.IO;

namespace _3DPresentation
{
  public partial class EditorView : Page
  {
      #region BienDungChung
      private string _strWorkingDirectory = string.Empty;
      private string _strWorkingDirectoryTemp;

      public string WorkingDirectory
      {
          get { return _strWorkingDirectory; }
          set
          {
              _strWorkingDirectory = value;
              WorkingDirectoryTemp = _strWorkingDirectory + "\\temp";
          }
      }

      public string WorkingDirectoryTemp
      {
          get { return _strWorkingDirectoryTemp; }
          set { _strWorkingDirectoryTemp = value; }
      }

      public void SetupWorkingDirectory()
      {
          if (WorkingDirectory == string.Empty)
          {
              WorkingDirectory = "d:\\\\test2";
          }

      }
      #endregion

      private Popup simplePopup = new Popup();

      public EditorView()
    {
      InitializeComponent();
      toolbar.ParentEditor = this;
      frameViewer.ParentView = this;
      odControl.ParentEditor = this;

      ArrFrame = new List<BaseModel>();

      //BaseModel newModel = PointModel.Import(new System.IO.FileInfo("d:\\NotDecreaseSameVertex_0000.ply"));
      //vcOjectViewer.AddModel(newModel);
      //vcOjectViewer.SetTarget(newModel);
    }

    // Executes when the user navigates to this page.
    protected override void OnNavigatedTo(NavigationEventArgs e)
    {
    }
      
    
    void OnImageSelected(object sender, ImageSelectedEventArgs e)
    {
        if (this.simplePopup.Child != null)
        {
            ((SimplePopupContent)this.simplePopup.Child).StopTimer();
        }
        currentImage.Source = e.Source;
        SimplePopupContent spc = new SimplePopupContent();
        spc.SelectedIndex = e.SelectedIndex;
        spc.ParentView = this;

        
        this.simplePopup.Child = spc;
        this.simplePopup.HorizontalOffset = frameViewer.ClickedPositionParent.X;
        this.simplePopup.VerticalOffset = frameViewer.ClickedPositionParent.Y;
        this.simplePopup.IsOpen = true;
    }

    void imageSelector_Loaded(object sender, RoutedEventArgs e)
    {

    }

    #region Popup
    public void DeleteFrame(int iIndex)
    {
        //delete
        frameViewer.DeleteImage(iIndex);
        vcOjectViewer.RemoveModel(_arrFrame[iIndex]);
        _arrFrame.RemoveAt(iIndex);
    }

    public void SetFixedImageIndex(int iIndex)
    {
        FixedImageIndex = iIndex;
    }

    public void SetReferenceImageIndex(int iIndex)
    {
        ReferenceImageIndex = iIndex;
    }

    public void ClosePopup()
    {
        this.simplePopup.IsOpen = false;
    }
    #endregion

    #region Fixed - Reference
    int iFixedImageIndex = -1;

    
    public int FixedImageIndex
    {
        get { return iFixedImageIndex; }
        set { iFixedImageIndex = value; }
    }
    int iReferenceImageIndex = -1;

    public int ReferenceImageIndex
    {
        get { return iReferenceImageIndex; }
        set { iReferenceImageIndex = value; }
    }
    #endregion

    #region Frame
    List<BaseModel> _arrFrame;
    

    public List<BaseModel> ArrFrame
    {
        get { return _arrFrame; }
        set { _arrFrame = value; }
    }

    private static object lockThis = new object();
    public void AddFrame(string strFrameName, PathUri pu)
    {
        FileInfo fi = new System.IO.FileInfo(strFrameName);
        AddFrame(fi, pu);
    }

    public void AddFrame(FileInfo fi, PathUri pu)
    {
        try
        {
            lock (lockThis)
            {
                BaseModel model = PointModel.Import(fi);
                ArrFrame.Add(model);
                vcOjectViewer.AddModel(ArrFrame[ArrFrame.Count - 1]);
                if (ArrFrame.Count == 1)
                {
                    vcOjectViewer.SetTarget(ArrFrame[ArrFrame.Count - 1]);
                }
                frameViewer.AddImage(pu);
            }
        }
        catch (Exception ex)
        {
            MessageBox.Show(ex.Message);
        }
    }

    public void SaveModel(string strFileName)
    {
        //call function save all frame
    }

    public void SaveFrame(string strFileName)
    {
        lock (lockThis)
        {
            //call function save all frame
            ArrFrame[frameViewer.SelectedIndex].Export(BaseModel.FileType.PLY, BaseModel.VertexType.XYZ_RGB, _3DPresentation.Utils.Global.GetRealFile(strFileName));
        }
    }

      //warning: rotation radian
    public void UpdateMatrixAfterFrame(int iIndex, Vector3 rotation, Vector3 Translation)
    {
        lock (lockThis)
        {
            for (int i = iIndex; i < ArrFrame.Count; i++)
            {
                ArrFrame[i].Rotation += rotation;
                ArrFrame[i].Position += Translation;
            }
        }
    }

    public void UpdateMatrixBeforeFrame(int iIndex, Vector3 rotation, Vector3 Translation)
    {
        lock (lockThis)
        {
            for (int i = iIndex; i <= iIndex; i++)
            {
                ArrFrame[i].Rotation += rotation;
                ArrFrame[i].Position += Translation;
            }
        }
    }
    #endregion
  }
}