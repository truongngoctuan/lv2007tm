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

        public override void Render()
        {
            if (IsEnable == false)
                return;
            try
            {
                base.Render();

                // Render model
                if (IsAddingModel)
                    return;

                Device.RasterizerState = new RasterizerState
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
                                model.SpecialMaterial.World = model.WorldMatrix;
                                model.SpecialMaterial.View = ActiveCamera.View;
                                model.SpecialMaterial.Projection = ActiveCamera.Projection;
                                model.SpecialMaterial.Device = Device;
                                model.Render(Device, true);
                            }
                            else
                            {
                                model.Material.World = model.WorldMatrix;
                                model.Material.View = ActiveCamera.View;
                                model.Material.Projection = ActiveCamera.Projection;
                                model.Material.Device = Device;
                                model.Render(Device, false);
                            }
                        }
                    }
                }                
                models = null;
            }
            catch (ArgumentException ex)
            {
                DrawError++;
            }

            if(Drawed != null)
                Drawed(this, EventArgs.Empty);
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
