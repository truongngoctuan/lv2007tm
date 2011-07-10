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
        private void PrepareRender()
        {
            EffectManager.InitEffects();
        }

        public void Render(GraphicsDevice graphicsDevice)
        {
            try
            {
                graphicsDevice.RasterizerState = new RasterizerState
                {
                    FillMode = FillMode.Solid,
                    CullMode = CullMode.None
                };

                lock (lockThis)
                {
                    foreach (BaseModel model in Models)
                    {
                        if (model.IsEnabled)
                        {
                            if (model is PointModel)
                                SetShaderEffect(EffectManager.ShaderEffects.PointEffect, graphicsDevice, model.WorldMatrix);
                            else
                                SetShaderEffect(EffectManager.ShaderEffects.NoEffect, graphicsDevice, model.WorldMatrix);
                            model.Render(graphicsDevice);
                        }
                    }
                }
            }
            catch (ArgumentException ex)
            {
                DrawError++;
            }
        }
        private void SetShaderEffect(EffectManager.ShaderEffects shaderEffect, GraphicsDevice graphicsDevice, Matrix world)
        {
            if (shaderEffect == EffectManager.ShaderEffects.NoEffect)
            {
                NoEffect noEffect = EffectManager.NoEffect;
                noEffect.World = world;
                noEffect.Projection = Camera.Projection;
                noEffect.View = Camera.View;

                noEffect.Device = graphicsDevice;
                noEffect.Apply();
            }
            else if (shaderEffect == EffectManager.ShaderEffects.TexturedNoEffect)
            {
                TexturedNoEffect texturedNoEffect = EffectManager.TexturedNoEffect;
                texturedNoEffect.World = world;
                texturedNoEffect.Projection = Camera.Projection;
                texturedNoEffect.View = Camera.View;

                texturedNoEffect.Device = graphicsDevice;
                texturedNoEffect.Apply();
            }
            else if (shaderEffect == EffectManager.ShaderEffects.PointEffect)
            {
                PointEffect pointEffect = EffectManager.PointEffect;
                pointEffect.World = world;
                pointEffect.Projection = Camera.Projection;
                pointEffect.View = Camera.View;
                pointEffect.Scale = new Vector2(1.0f / SurfaceSize.X, 1.0f / SurfaceSize.Y);

                pointEffect.Device = graphicsDevice;
                pointEffect.Apply();
            }
        }
    }
}
