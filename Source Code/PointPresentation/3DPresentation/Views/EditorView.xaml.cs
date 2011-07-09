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

namespace _3DPresentation
{
  public partial class EditorView : Page
  {
      #region BienDungChung
      private string _strWorkingDirectory;
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
        currentImage.Source = e.Source;
        SimplePopupContent spc = new SimplePopupContent();
        spc.ParentView = this;

        this.simplePopup.Child = spc;
        this.simplePopup.HorizontalOffset = frameViewer.ClickedPositionParent.X;
        this.simplePopup.VerticalOffset = frameViewer.ClickedPositionParent.Y;
        this.simplePopup.IsOpen = true;
    }

    void imageSelector_Loaded(object sender, RoutedEventArgs e)
    {
        frameViewer.SetImages(new string[]
            {
                "Images/j0149013.jpg",
                "Images/j0182516.jpg",
                "Images/j0262524.jpg"
                //,
                //"Images/j0309223.jpg",
                //"Images/j0314069.jpg",
                //"Images/j0402444.jpg",
                //"Images/j0406500.jpg",
                //"Images/j0406702.jpg",
                //"Images/j0407544.jpg",
                //"Images/j0422769.jpg",
                //"Images/j0428653.jpg",
                //"Images/j0314059.jpg",
                //"Images/j0430836.jpg",
                //"Images/j0431767.jpg",
                //"Images/j0433157.jpg"
            });
    }

    #region Popup
    public void DeleteFrame()
    {
        //delete
        frameViewer.DeleteImage(frameViewer.SelectedIndex);
    }

    public void SetFixedImageIndex()
    {
        FixedImageIndex = frameViewer.SelectedIndex;
    }

    public void SetReferenceImageIndex()
    {
        ReferenceImageIndex = frameViewer.SelectedIndex;
    }

    public void ClosePopup()
    {
        this.simplePopup.IsOpen = false;
    }
    #endregion
    public void AddFrame(int iIndex)
    {
        //add
    }

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

  }
}