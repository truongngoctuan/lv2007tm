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
        // Events

        private void PrepareRender()
        {
            EffectManager.InitEffects();
        }

        private void Render(GraphicsDevice graphicsDevice)
        {
            graphicsDevice.RasterizerState = new RasterizerState
            {
                FillMode = FillMode.Solid,
                CullMode = CullMode.None
            };

            BaseModel[] models;
            lock (lockThis)
            {
                models = customSceneModels.ToArray();
            }
            foreach (BaseModel model in models)
            {
                if (model.IsEnabled)
                {
                    if (ActiveCamera.IsInFrustrum(model.BoundingInfo))
                    {
                        if (model == selectedMesh)
                        {
                            model.Render(graphicsDevice, true);
                        }
                        else
                        {
                            model.Render(graphicsDevice, false);
                        }
                    }
                }
            }                
            models = null;
        }
    }
}
