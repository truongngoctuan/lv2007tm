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
    public partial class CustomScene : Babylon.Scene
    {
        // Models
        List<BaseModel> customSceneModels = new List<BaseModel>();
        BaseModel selectedMesh = null;

        private void PrepareModels()
        {
            // Models            
        }

        public bool AddModel(BaseModel model)
        {
            if (model == null)
                return false;
            if (model.IsLoaded == false)
                return false;
            if (customSceneModels.Contains(model))
                return false;

            IsAddingModel = true;
            customSceneModels.Add(model);
            IsAddingModel = false;
            return true;
        }

        public bool RemoveModel(BaseModel model)
        {
            return customSceneModels.Remove(model);
        }

        public BaseModel[] GetModels()
        {
            return customSceneModels.ToArray();
        }

        public BaseModel AddModel(FileInfo file)
        {
            BaseModel model = BaseModel.Import(file);
            if (model == null)
                return null;

            //model.InitBuffers(Device);
            AddModel(model);

            model.Position = new Vector3(-7.0f, 1.8f, 8.0f);
            return model;
        }

        public BaseModel CheckPicking(Point mouse, Vector2 drawingSurfaceSize)
        {
            if (IsLoaded == false)
                return null;
            BaseModel selectedModel = null;
            Ray ray = Babylon.Utilities.CreateRay((float)mouse.X, (float)mouse.Y, (float)drawingSurfaceSize.X, (float)drawingSurfaceSize.Y, Matrix.Identity, ActiveCamera.View, ActiveCamera.Projection);
            
            float selectedDistance = float.MaxValue;
            foreach (BaseModel mesh in customSceneModels)
            {
                float? distance = ray.Intersects(mesh.BoundingInfo.BoundingBoxWorld);
                if (distance.HasValue == false)
                    continue;

                if (distance < selectedDistance)
                {
                    selectedDistance = distance.Value;
                    selectedModel = mesh;
                }
            }
            if (selectedDistance == float.MaxValue)
            {
                selectedModel = null;
            }
            return selectedModel;

            //basicEffect.EmissiveColor = mesh == selectedMesh ? new Color(0.5f, 0.5f, 0.5f, 0) : Color.Black;
        }
    }
}
