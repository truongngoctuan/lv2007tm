﻿using System;
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
using System.Reflection;

namespace _3DPresentation
{
    public partial class MaterialSelectorControl : UserControl
    {
        BaseModel target;
        public MaterialSelectorControl()
        {
            InitializeComponent();
        }

        void cbMaterialType_SelectionChanged(object sender, SelectionChangedEventArgs e)
        {
            if (target == null)
                return;
            if (cbMaterialType.SelectedItem is MaterialType)
            {
                Type type = ((MaterialType)cbMaterialType.SelectedItem).Type;
                //if (target.Material.GetType() != type || propertiesPanel.Target == null)
                {
                    if (type.BaseType == typeof(BaseMaterial))
                    {
                        BaseMaterial material = null;
                        try
                        {
                            if (type != target.Material.GetType())
                                material = (BaseMaterial)Activator.CreateInstance(type);
                            else
                                material = target.Material;
                            target.Material = material;
                            propertiesPanel.Target = (INotifyPropertyChanged)material;
                        }
                        catch (Exception ex)
                        {
                            MessageBox.Show(ex.Message);
                        }                        
                    }                    
                }
            }
        }

        public void SetTarget(BaseModel model)
        {
            if (model == null)
            {
                target = null;
                propertiesPanel.Target = null;
                return;
            }
            
            if (model != null)
            {
                cbMaterialType.SelectionChanged -= new SelectionChangedEventHandler(cbMaterialType_SelectionChanged);
                target = model;
                Type[] materialTypes = model.GetCompatibleMaterialTypes();
                //cbMaterialType.Items.Clear();
                
                //cbMaterialType.DisplayMemberPath = "Name";

                MaterialType[] types = new MaterialType[materialTypes.Length];

                for (int i = 0; i < materialTypes.Length; i++)
                {
                    types[i] = new MaterialType();
                    types[i].Type = materialTypes[i];
                    types[i].Name = BaseMaterial.GetName(materialTypes[i]);
                    //cbMaterialType.Items.Add(materialType);
                }
                cbMaterialType.ItemsSource = types;
                cbMaterialType.DisplayMemberPath = "Name";

                materialTypes = null;
                types = null;
                cbMaterialType.SelectionChanged += new SelectionChangedEventHandler(cbMaterialType_SelectionChanged);
                cbMaterialType.SelectedItem = target.Material.GetType();
            }            
        }

        public class MaterialType
        {
            public Type Type { get; set; }
            public string Name { get; set; }
        }
    }
}