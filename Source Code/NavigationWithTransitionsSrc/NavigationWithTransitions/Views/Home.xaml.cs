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
using NavigationWithTransitions.CustomHomeChildWindow;


namespace NavigationWithTransitions
{
  public partial class Home : Page
  {
    public Home()
    {
      InitializeComponent();
    }

    // Executes when the user navigates to this page.
    protected override void OnNavigatedTo(NavigationEventArgs e)
    {
    }

    CustomChildWindow cw = new CustomChildWindow();

    private void Button_Click(object sender, RoutedEventArgs e)
    {
        //SilverlightMessageBoxLibrary.Message.InfoMessage("asdasd");
        //SilverlightMessageBoxLibrary.CustomMessage asd = new SilverlightMessageBoxLibrary.CustomMessage("aaa", SilverlightMessageBoxLibrary.CustomMessage.MessageType.Confirm, null);
        //asd.Show();

        
        cw.Closed += new EventHandler(cw_Closed);
        cw.Show();
    }

    void cw_Closed(object sender, EventArgs e)
    {
        //throw new NotImplementedException();
        if ((bool)cw.DialogResult)
        {
            SilverlightMessageBoxLibrary.Message.InfoMessage("Click Button OK");
        }
        else
        {
            SilverlightMessageBoxLibrary.Message.InfoMessage("Click Button Cancel");
        }
        cw.Closed -= cw_Closed;
    }

    void OnImageSelected(object sender, ImageSelectedEventArgs e)
    {
        currentImage.Source = e.Source;
    }

    void imageSelector_Loaded(object sender, RoutedEventArgs e)
    {
        frameViewer.SetImages(new string[]
            {
                "Images/j0149013.jpg",
                "Images/j0182516.jpg",
                "Images/j0262524.jpg",
                "Images/j0309223.jpg",
                "Images/j0314069.jpg",
                "Images/j0402444.jpg",
                "Images/j0406500.jpg",
                "Images/j0406702.jpg",
                "Images/j0407544.jpg",
                "Images/j0422769.jpg",
                "Images/j0428653.jpg",
                "Images/j0314059.jpg",
                "Images/j0430836.jpg",
                "Images/j0431767.jpg",
                "Images/j0433157.jpg"
            });
    }

    private void btSetupSDK_Click(object sender, RoutedEventArgs e)
    {
        cwSetupSDK cwNew = new cwSetupSDK();
        cwNew.Show();
    }

    private void btSetupWorkSpace_Click(object sender, RoutedEventArgs e)
    {
        cwSetupWorkSpace cwNew = new cwSetupWorkSpace();
        cwNew.Show();
    }

    private void btResetWorkSpace_Click(object sender, RoutedEventArgs e)
    {
        cwResetWorkSpace cwNew = new cwResetWorkSpace();
        cwNew.Show();
    }

    private void btOpenModel_Click(object sender, RoutedEventArgs e)
    {
        cwOpenModel cwNew = new cwOpenModel();
        cwNew.Show();
    }

    private void btSaveModel_Click(object sender, RoutedEventArgs e)
    {
        cwSaveModel cwNew = new cwSaveModel();
        cwNew.Show();
    }

    private void btOptimize_Click(object sender, RoutedEventArgs e)
    {
        cwOptimize cwNew = new cwOptimize();
        cwNew.Show();
    }
  }
}