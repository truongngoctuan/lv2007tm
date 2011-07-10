using _3DPresentation.Effects;
using System.Collections.Generic;
using _3DPresentation.Models;
using Microsoft.Xna.Framework.Graphics;
using System;
using Microsoft.Xna.Framework;
using System.IO;
using System.Windows.Threading;
using System.Windows;

namespace _3DPresentation
{
    public partial class ViewScene
    {
        private object lockThis = new object();
        List<BaseModel> Models = new List<BaseModel>();
        private void PrepareModels()
        {
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
                    result = false;
            }
            if (result)
            {
                TargetModel = model;
                Camera.Radius = TargetModel.BoundingInfo.BoundingSphereWorld.Radius * 2.0f;
                Camera.Target = TargetModel.BoundingInfo.BoundingSphereWorld.Center;
            }
            return result;
        }
    }
}
