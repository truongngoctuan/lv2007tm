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
using _3DPresentation.Material;
using System.ComponentModel;

namespace _3DPresentation
{
    public partial class MaterialSelectorControl : UserControl
    {
        BaseModel target;
        public MaterialSelectorControl()
        {
            InitializeComponent();
            

            cbMaterialType.Items.Add(typeof(NoEffectMaterial));
            cbMaterialType.Items.Add(typeof(TexturedMaterial));
            cbMaterialType.Items.Add(typeof(PointMaterial));
        }

        void cbMaterialType_SelectionChanged(object sender, SelectionChangedEventArgs e)
        {
            if (target == null)
                return;
            if (cbMaterialType.SelectedItem is Type)
            {
                Type type = (Type)cbMaterialType.SelectedItem;
                if (target.Material.GetType() != type || propertiesPanel.Target == null)
                {
                    BaseMaterial material = null;
                    if (type == typeof(NoEffectMaterial))
                    {
                        material = new NoEffectMaterial();
                    }
                    else if (type == typeof(TexturedMaterial))
                    {
                        material = new TexturedMaterial();
                    }
                    else if (type == typeof(PointMaterial))
                    {
                        material = new PointMaterial();
                    }
                    target.Material = material;
                    propertiesPanel.Target = (INotifyPropertyChanged)material;
                }
            }
        }

        public void SetTarget(BaseModel model)
        {
            cbMaterialType.SelectionChanged -= new SelectionChangedEventHandler(cbMaterialType_SelectionChanged);

            target = model;
            Type[] materialTypes = model.GetCompatibleMaterialTypes();
            cbMaterialType.Items.Clear();
            foreach (Type materialType in materialTypes)
            {
                cbMaterialType.Items.Add(materialType);
            }            

            cbMaterialType.SelectionChanged += new SelectionChangedEventHandler(cbMaterialType_SelectionChanged);            
            cbMaterialType.SelectedItem = target.Material.GetType();

            materialTypes = null;
            //SetMaterial(target.Material);
        }

        private void SetMaterial(BaseMaterial property)
        {
            if (property is INotifyPropertyChanged)
            {
                if(target.Material.GetType() != property.GetType())
                    target.Material = property;
                propertiesPanel.Target = (INotifyPropertyChanged)target.Material;
            }
        }
    }
}
