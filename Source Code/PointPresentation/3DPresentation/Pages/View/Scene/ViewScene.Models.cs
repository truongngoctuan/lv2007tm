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
        private static object lockThis = new object();
        List<BaseModel> Models = new List<BaseModel>();
        private void PrepareModels()
        {
        }

        public bool AddModel(BaseModel model)
        {
            if (model.IsLoaded == false)
                return false;
            if (Models.Contains(model))
                return true;

            lock (lockThis)
            {
                Models.Add(model);
                if (Models.Count == 1)
                    SetTarget(model);
            }
            return true;
        }

        public bool RemoveModel(BaseModel model)
        {
            if (model == null)
                return false;
            if (Models.Contains(model) == false)
                return false;
            bool result = false; 
            lock (lockThis)
            {
                result = Models.Remove(model);
            }
            return result;
        }

        public void ClearModels()
        {
            Models.Clear();
        }

        public bool SetTarget(BaseModel model)
        {
            if (model == null)
                return false;
            if (Models.Contains(model) == false)
                return false;

            TargetModel = model;
            Camera.Radius = TargetModel.BoundingInfo.BoundingSphereWorld.Radius * 2.0f;
            Camera.Target = TargetModel.BoundingInfo.BoundingSphereWorld.Center;
            return true;
        }
    }
}
