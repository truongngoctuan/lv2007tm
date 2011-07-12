using System.Windows.Controls;
using System;
using System.ComponentModel;
using System.Reflection;

namespace _3DPresentation.PropertyPanel
{
    public class NumberEditor : ContentControl
    {
        Label label;
        TextBox editor;

        INotifyPropertyChanged Listener { get; set; }
        string PropertyName { get; set; }
        object PropertyValue { get; set; }
        Type ValueType { get; set; }

        PropertyInfo Property;
        object Instance;
        public NumberEditor(INotifyPropertyChanged feeder, PropertyInfo property, object instance)
        {
            Listener = feeder;

            label = new Label();
            editor = new TextBox();

            Property = property;
            Instance = instance;

            PropertyName = property.Name;
            PropertyValue = property.GetValue(instance, null);
            ValueType = property.GetType();

            feeder.PropertyChanged += new PropertyChangedEventHandler(feeder_PropertyChanged);
            editor.TextChanged += new TextChangedEventHandler(editor_TextChanged);
        }

        void editor_TextChanged(object sender, TextChangedEventArgs e)
        {
            Property.SetValue(Instance, PropertyValue, null);
        }

        void feeder_PropertyChanged(object sender, PropertyChangedEventArgs e)
        {
            
        }

        public void SetLabel(string text)
        {
            PropertyName = text;
        }
        public void SetValue(object newValue)
        {
            PropertyValue = newValue;

        }
        public void SetValue(string text)
        {
            if (PropertyValue.GetType() == typeof(int))
            {
                int value;
                if (int.TryParse(text, out value))
                    SetValue(value);
            }
            else if (PropertyValue.GetType() == typeof(float))
            {
                float value;
                if (float.TryParse(text, out value))
                    SetValue(value);
            }
            if (PropertyValue.GetType() == text.GetType())
            {
                PropertyValue = text;
            }
        }

        public void UpdateContent()
        {
            Dispatcher.BeginInvoke(new Action(() => 
            {
                label.Content = PropertyName;
                editor.Text = PropertyValue.ToString();
            }));
        }
    }
}
