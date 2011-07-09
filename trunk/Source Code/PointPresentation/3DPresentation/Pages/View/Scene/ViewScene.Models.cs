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

            Models.Add(model);
            return true;
        }

        public bool RemoveModel(BaseModel model)
        {
            if (model == null)
                return false;
            if (Models.Contains(model) == false)
                return false;
            return Models.Remove(model);
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
