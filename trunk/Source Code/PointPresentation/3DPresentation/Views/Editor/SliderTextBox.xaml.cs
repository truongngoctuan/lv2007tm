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

namespace _3DPresentation.Views.Editor
{
    public partial class SliderTextBox : UserControl
    {
        public SliderTextBox()
        {
            InitializeComponent();
        }

        //http://www.silverlightshow.net/items/Attached-Properties-in-Silverlight.aspx
        //#region Min
        //public static readonly DependencyProperty MinProperty = DependencyProperty.RegisterAttached(
        //"Min",                   //Name of the property
        //typeof(float),              //Type of the property
        //typeof(SliderTextBox),    // Type of the provider of the registered attached property
        //        null);                           //Callback invoked in case the property value has changed

        //public static void SetMin( DependencyObject obj, float min )
        //{
        //    obj.SetValue(MinProperty, min);
        //}
 
        //public static float GetMin( DependencyObject obj )
        //{
        //    return (float)obj.GetValue(MinProperty);
        //}
        //#endregion

        cwMatchModelManual _parent = null;
        string strKey = string.Empty;
        public void setParams(cwMatchModelManual parent, string Key, string strLabel, float fMin, float fMax, float fDefaultValue)
        {
            _parent = parent;
            strKey = Key;
            tblock.Text = strLabel;
            sd.Minimum = fMin;
            sd.Maximum = fMax;
            tbox.Text = fDefaultValue.ToString();
        }

        private void sd_ValueChanged(object sender, RoutedPropertyChangedEventArgs<double> e)
        {
            tbox.Text = ((int)sd.Value).ToString();

            this._parent.OnValueChange(strKey, (float)sd.Value);
        }

        private void tbox_TextChanged(object sender, TextChangedEventArgs e)
        {
            double iResult = 0;
            if (double.TryParse(tbox.Text, out iResult))
            {
                sd.Value = iResult;
            }

        }


        public float Value
        {
            get { return (float)sd.Value; }
        }
    }
}
