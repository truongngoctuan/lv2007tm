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

namespace _3DPresentation
{
    public partial class MySliderControl : UserControl
    {
        public MySliderControl()
        {
            InitializeComponent();
            mSlider.ValueChanged += new RoutedPropertyChangedEventHandler<double>(mSlider_ValueChanged);
            mValue.LostFocus += new RoutedEventHandler(mValue_LostFocus);
            mValue.KeyDown += new KeyEventHandler(mValue_KeyDown);
        }

        void mValue_KeyDown(object sender, KeyEventArgs e)
        {
            //char c = (char)e.PlatformKeyCode;
            //if (!(char.IsDigit(c) || c == '.' || c == '-'))
            //    e.Handled = true;
            if (e.Key == Key.Enter)
            {
                double temp = Value;
                if (double.TryParse(mValue.Text, out temp))
                {
                    Value = temp;
                }
            }
        }

        void mValue_LostFocus(object sender, RoutedEventArgs e)
        {
            double temp = Value;
            if (double.TryParse(mValue.Text, out temp))
            {
                Value = temp;
            }
        }

        void mSlider_ValueChanged(object sender, RoutedPropertyChangedEventArgs<double> e)
        {
            Value = (float)mSlider.Value;
        }

        public string Title
        {
            get
            {
                return mTitle.Text.ToString();
            }
            set
            {
                mTitle.Text = value;
            }
        }

        private double _value;
        public double Value
        {
            get
            {
                return _value;
            }
            set
            {
                double oldValue = _value;
                if (value > MaxValue)
                    _value = MaxValue;
                else if (value < MinValue)
                    _value = MinValue;
                else
                    _value = value;
                OnValueChanged(new ValueChangedEventArgs(_value, oldValue));
            }
        }

        public double MinValue
        {
            get
            {
                return mSlider.Minimum;
            }
            set
            {
                mSlider.Minimum = value;
            }
        }

        public double MaxValue
        {
            get
            {
                return mSlider.Maximum;
            }
            set
            {
                mSlider.Maximum = value;
            }
        }

        private void OnValueChanged(ValueChangedEventArgs e)
        {            
            mSlider.Value = _value;
            mValue.Text = _value.ToString("0.00");

            if(this.ValueChanged != null)
                ValueChanged(this, e);
        }

        public delegate void ValueChangedEventHandler(object sender, ValueChangedEventArgs e);
        public event ValueChangedEventHandler ValueChanged;

        public class ValueChangedEventArgs : EventArgs
        {
            public double NewValue
            {
                get;
                set;
            }
            public double OldValue
            {
                get;
                set;
            }

            public ValueChangedEventArgs(double newValue, double oldValue) : base()
            {
                NewValue = newValue;
                OldValue = oldValue;
            }
        }
    }
}
