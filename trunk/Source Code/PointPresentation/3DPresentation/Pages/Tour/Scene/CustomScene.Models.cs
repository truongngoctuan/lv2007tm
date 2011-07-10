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
        private object lockThis = new object();
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

            bool result = false;
            lock (lockThis)
            {
                if (customSceneModels.Contains(model))
                    result = false;
                else
                {
                    customSceneModels.Add(model);
                    result = true;
                }
            }
            return result;
        }

        public bool RemoveModel(BaseModel model)
        {
            bool result = false;
            lock (lockThis)
            {
                result = customSceneModels.Remove(model);
            }
            return result;
        }

        public BaseModel[] GetModels()
        {
            BaseModel[] result = null;
            lock (lockThis)
            {
                result = customSceneModels.ToArray();
            }
            return result;
        }

        public BaseModel CheckPicking(Point mouse, Vector2 drawingSurfaceSize)
        {
            if (IsLoaded == false)
                return null;
            BaseModel selectedModel = null;
            Ray ray = Babylon.Utilities.CreateRay((float)mouse.X, (float)mouse.Y, (float)drawingSurfaceSize.X, (float)drawingSurfaceSize.Y, Matrix.Identity, ActiveCamera.View, ActiveCamera.Projection);
            
            float selectedDistance = float.MaxValue;

            BaseModel[] meshes;
            lock (lockThis)
            {
                meshes = customSceneModels.ToArray();
            }
            foreach (BaseModel mesh in meshes)
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
            meshes = null;

            if (selectedDistance == float.MaxValue)
            {
                selectedModel = null;
            }
            return selectedModel;

            //basicEffect.EmissiveColor = mesh == selectedMesh ? new Color(0.5f, 0.5f, 0.5f, 0) : Color.Black;
        }
    }
}
