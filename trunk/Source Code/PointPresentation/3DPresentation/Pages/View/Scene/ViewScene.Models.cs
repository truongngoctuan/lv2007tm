using _3DPresentation.Effects;
using System.Collections.Generic;
using _3DPresentation.Models;
using Microsoft.Xna.Framework.Graphics;
using System;
using Microsoft.Xna.Framework;
using System.IO;
using System.Windows.Threading;
using System.Windows;
using _3DPresentation.Material;

namespace _3DPresentation
{
    public partial class ViewScene
    {
        private object lockThis = new object();
        List<BaseModel> Models = new List<BaseModel>();

        BaseModel PointLight;
        SimpleEffectMaterial PointLightMaterial;
        PointLightInfomation[] PointLightInfomations;
        struct PointLightInfomation
        {
            public Vector3 Position;
            public GlobalVars.ColorEnum Color;
            public bool Enable;
        }
        private void PrepareModels()
        {
            PointLight = BaseModel.Import(Utils.Global.GetPackStream("Resources/sphere.ply"), BaseModel.FileType.PLY);
            PointLightMaterial = new SimpleEffectMaterial();
            PointLight.Material = PointLightMaterial;

            PointLightInfomations = new PointLightInfomation[4];
        }

        public void SetLightPosition(int index, Vector3 position, GlobalVars.ColorEnum color)
        {
            if (index < PointLightInfomations.Length)
            {
                if (TargetModel != null)
                    PointLight.Scale = 0.1f * TargetModel.BoundingInfo.BoundingSphereWorld.Radius;
                PointLightInfomations[index].Position = position;
                PointLightInfomations[index].Color = color;
                PointLightInfomations[index].Enable = true;
            }
        }

        public bool AddModel(BaseModel model)
        {
            if (model.IsLoaded == false)
                return false;
            bool result = false;
            lock (lockThis)
            {
                if (Models.Contains(model))
                    result = true;
                else
                {
                    Models.Add(model);
                    if (Models.Count == 1)
                        SetTarget(model);
                    result = true;
                }
            }
            return result;
        }

        public bool RemoveModel(BaseModel model)
        {
            if (model == null)

                return false;
            bool result = false;
            lock (lockThis)
            {
                if (Models.Contains(model) == false)
                    result = false;
                else
                    result = Models.Remove(model);
            }
            return result;
        }

        public void ClearModels()
        {
            lock (lockThis)
            {
                Models.Clear();
            }
        }

        public bool SetTarget(BaseModel model)
        {
            if (model == null)
                return false;
            bool result = false;
            lock (lockThis)
            {
                if (Models.Contains(model))
                {
                    result = true;
                    TargetModel = model;
                    Camera.Radius = TargetModel.BoundingInfo.BoundingSphereWorld.Radius * 4.0f;
                    Camera.Target = TargetModel.BoundingInfo.BoundingSphereWorld.Center;
                    Camera.Alpha = Camera.Alpha; // to raise event => recompute Position to get new ViewMatrix
                }
            }
            return result;
        }

        public BaseModel[] GetModels()
        {
            return Models.ToArray();
        }
    }
}
