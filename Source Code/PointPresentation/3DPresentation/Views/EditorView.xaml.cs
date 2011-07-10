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
        spc.ParentView = this;

        
        this.simplePopup.Child = spc;
        this.simplePopup.HorizontalOffset = frameViewer.ClickedPositionParent.X;
        this.simplePopup.VerticalOffset = frameViewer.ClickedPositionParent.Y;
        this.simplePopup.IsOpen = true;
    }

    void imageSelector_Loaded(object sender, RoutedEventArgs e)
    {
        try{

        List<string> arrFrameName = new List<string>();
                arrFrameName.Add("d:\\NotDecreaseSameVertex_0000.ply");
                arrFrameName.Add("d:\\NotDecreaseSameVertex_0005.ply");
                arrFrameName.Add("d:\\NotDecreaseSameVertex_0015.ply");
                arrFrameName.Add("d:\\NotDecreaseSameVertex_0025.ply");
                arrFrameName.Add("d:\\NotDecreaseSameVertex_0035.ply");
                arrFrameName.Add("d:\\NotDecreaseSameVertex_0045.ply");
                arrFrameName.Add("d:\\NotDecreaseSameVertex_0055.ply");
                arrFrameName.Add("d:\\NotDecreaseSameVertex_0065.ply");

                List<string> arrFrameThumnail = new List<string>();
                arrFrameThumnail.Add("d:\\NotDecreaseSameVertex_0000.jpg");
                arrFrameThumnail.Add("d:\\NotDecreaseSameVertex_0005.jpg");
                arrFrameThumnail.Add("d:\\NotDecreaseSameVertex_0015.jpg");
                arrFrameThumnail.Add("d:\\NotDecreaseSameVertex_0025.jpg");
                arrFrameThumnail.Add("d:\\NotDecreaseSameVertex_0035.jpg");
                arrFrameThumnail.Add("d:\\NotDecreaseSameVertex_0045.jpg");
                arrFrameThumnail.Add("d:\\NotDecreaseSameVertex_0055.jpg");
                arrFrameThumnail.Add("d:\\NotDecreaseSameVertex_0065.jpg");

                for (int i = 0; i < 4; i++)
                {
                    this.AddFrame(arrFrameName[i], arrFrameThumnail[i]);
                    //System.Threading.Thread.Sleep(2000);
                }


                }
                catch (Exception ex)
                {
                    MessageBox.Show(ex.Message);
                }

        //frameViewer.SetImages(new PathUri[]
        //    {
        //        new PathUri("Views/Editor/Images/j0149013.jpg", false),
        //        new PathUri("Views/Editor/Images/j0182516.jpg", false),
        //        new PathUri("Views/Editor/Images/j0262524.jpg", false),
        //        //ImageSelector.UriToBitmapImage("Images/j0149013.jpg"),
        //        //ImageSelector.UriToBitmapImage("Images/j0182516.jpg"),
        //        //ImageSelector.UriToBitmapImage("Images/j0262524.jpg")
        //        //,
        //        //"Images/j0309223.jpg",
        //        //"Images/j0314069.jpg",
        //        //"Images/j0402444.jpg",
        //        //"Images/j0406500.jpg",
        //        //"Images/j0406702.jpg",
        //        //"Images/j0407544.jpg",
        //        //"Images/j0422769.jpg",
        //        //"Images/j0428653.jpg",
        //        //"Images/j0314059.jpg",
        //        //"Images/j0430836.jpg",
        //        //"Images/j0431767.jpg",
        //        //"Images/j0433157.jpg"
        //    });
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
    public void AddFrame(string strFrameName, string strThumnailName)
    {
        FileInfo fi = new System.IO.FileInfo(strFrameName);
        AddFrame(fi, strThumnailName);
    }

    public void AddFrame(FileInfo fi, string strThumnailName)
    {
        try
        {
            lock (ArrFrame)
            {
                BaseModel model = PointModel.Import(fi);
                ArrFrame.Add(model);
                vcOjectViewer.AddModel(ArrFrame[ArrFrame.Count - 1]);
                if (ArrFrame.Count == 1)
                {
                    vcOjectViewer.SetTarget(ArrFrame[ArrFrame.Count - 1]);
                }
                frameViewer.AddImage(new PathUri(strThumnailName, true));
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

    private void asd(object sender, RoutedEventArgs e)
    {
        List<string> arrFrameName = new List<string>();
        arrFrameName.Add("d:\\NotDecreaseSameVertex_0000.ply");
        arrFrameName.Add("d:\\NotDecreaseSameVertex_0005.ply");
        arrFrameName.Add("d:\\NotDecreaseSameVertex_0015.ply");
        arrFrameName.Add("d:\\NotDecreaseSameVertex_0025.ply");
        arrFrameName.Add("d:\\NotDecreaseSameVertex_0035.ply");
        arrFrameName.Add("d:\\NotDecreaseSameVertex_0045.ply");
        arrFrameName.Add("d:\\NotDecreaseSameVertex_0055.ply");
        arrFrameName.Add("d:\\NotDecreaseSameVertex_0065.ply");

        List<string> arrFrameThumnail = new List<string>();
        arrFrameThumnail.Add("d:\\NotDecreaseSameVertex_0000.jpg");
        arrFrameThumnail.Add("d:\\NotDecreaseSameVertex_0005.jpg");
        arrFrameThumnail.Add("d:\\NotDecreaseSameVertex_0015.jpg");
        arrFrameThumnail.Add("d:\\NotDecreaseSameVertex_0025.jpg");
        arrFrameThumnail.Add("d:\\NotDecreaseSameVertex_0035.jpg");
        arrFrameThumnail.Add("d:\\NotDecreaseSameVertex_0045.jpg");
        arrFrameThumnail.Add("d:\\NotDecreaseSameVertex_0055.jpg");
        arrFrameThumnail.Add("d:\\NotDecreaseSameVertex_0065.jpg");

        for (int i = 0; i < 1; i++)
        {
            this.AddFrame(arrFrameName[i], arrFrameThumnail[i]);
            //System.Threading.Thread.Sleep(2000);
        }


        //this.Dispatcher.BeginInvoke(new Action(() =>
        //{

        //    try
        //    {
        //        List<string> arrFrameName = new List<string>();
        //        arrFrameName.Add("d:\\NotDecreaseSameVertex_0000.ply");
        //        arrFrameName.Add("d:\\NotDecreaseSameVertex_0005.ply");
        //        arrFrameName.Add("d:\\NotDecreaseSameVertex_0015.ply");
        //        arrFrameName.Add("d:\\NotDecreaseSameVertex_0025.ply");
        //        arrFrameName.Add("d:\\NotDecreaseSameVertex_0035.ply");
        //        arrFrameName.Add("d:\\NotDecreaseSameVertex_0045.ply");
        //        arrFrameName.Add("d:\\NotDecreaseSameVertex_0055.ply");
        //        arrFrameName.Add("d:\\NotDecreaseSameVertex_0065.ply");

        //        List<string> arrFrameThumnail = new List<string>();
        //        arrFrameThumnail.Add("d:\\NotDecreaseSameVertex_0000.jpg");
        //        arrFrameThumnail.Add("d:\\NotDecreaseSameVertex_0005.jpg");
        //        arrFrameThumnail.Add("d:\\NotDecreaseSameVertex_0015.jpg");
        //        arrFrameThumnail.Add("d:\\NotDecreaseSameVertex_0025.jpg");
        //        arrFrameThumnail.Add("d:\\NotDecreaseSameVertex_0035.jpg");
        //        arrFrameThumnail.Add("d:\\NotDecreaseSameVertex_0045.jpg");
        //        arrFrameThumnail.Add("d:\\NotDecreaseSameVertex_0055.jpg");
        //        arrFrameThumnail.Add("d:\\NotDecreaseSameVertex_0065.jpg");

        //        for (int i = 0; i < 1; i++)
        //        {
        //            this.AddFrame(arrFrameName[i], arrFrameThumnail[i]);
        //            //System.Threading.Thread.Sleep(2000);
        //        }
        //    }
        //    catch (Exception ex)
        //    {
        //        MessageBox.Show(ex.Message);
        //    }
        //}));
    }

  }
}