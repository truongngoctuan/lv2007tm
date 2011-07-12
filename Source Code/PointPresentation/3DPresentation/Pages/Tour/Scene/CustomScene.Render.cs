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
        public event EventHandler Drawed;
        public int DrawError { get; private set; }

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
                        //if (model == selectedMesh)
                        //    SetShaderEffect(EffectManager.ShaderEffects.TexturedNoEffect, model.WorldMatrix);
                        //else
                        //    SetShaderEffect(EffectManager.ShaderEffects.NoEffect, model.WorldMatrix);
                        //model.Render(Device);
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

        private void SetShaderEffect(EffectManager.ShaderEffects shaderEffect, Matrix world)
        {
            if (shaderEffect == EffectManager.ShaderEffects.NoEffect)
            {
                NoEffect noEffect = EffectManager.NoEffect;
                noEffect.World = world;
                noEffect.Projection = ActiveCamera.Projection;
                noEffect.View = ActiveCamera.View;

                noEffect.Device = Device;
                noEffect.Apply();
            }
            else if (shaderEffect == EffectManager.ShaderEffects.TexturedNoEffect)
            {
                TexturedNoEffect texturedNoEffect = EffectManager.TexturedNoEffect;
                texturedNoEffect.World = world;
                texturedNoEffect.Projection = ActiveCamera.Projection;
                texturedNoEffect.View = ActiveCamera.View;

                texturedNoEffect.Device = Device;
                texturedNoEffect.Apply();
            }
        }
    }
}
