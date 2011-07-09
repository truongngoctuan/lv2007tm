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
        // Effects
        private enum ShaderEffect { NoEffect, TexturedNoEffect };
        NoEffect noEffect;
        TexturedNoEffect texturedNoEffect;

        private void PrepareRender()
        {
            noEffect = new NoEffect(resourceDevice);
            texturedNoEffect = new TexturedNoEffect(resourceDevice);

            Surface.Dispatcher.BeginInvoke(() =>
            {
                texturedNoEffect.DiffuseTexture = Utils.Global.LoadTexture("Images/3.jpg", resourceDevice);
            });
        }

        public void Render(GraphicsDevice graphicsDevice)
        {
            // Render model
            if (IsAddingModel)
                return;

            graphicsDevice.RasterizerState = new RasterizerState
            {
                FillMode = FillMode.Solid,
                CullMode = CullMode.None
            };

            foreach (BaseModel model in Models)
            {
                if (model.IsEnabled)
                {
                    SetShaderEffect(ShaderEffect.NoEffect, graphicsDevice, model.WorldMatrix);
                    model.Render(graphicsDevice);
                }
            }
        }

        private void SetShaderEffect(ShaderEffect shaderEffect, GraphicsDevice graphicsDevice, Matrix world)
        {
            if (shaderEffect == ShaderEffect.NoEffect)
            {
                noEffect.World = world;
                noEffect.Projection = Camera.Projection;
                noEffect.View = Camera.View;

                noEffect.Device = graphicsDevice;
                noEffect.Apply();
            }
            else if (shaderEffect == ShaderEffect.TexturedNoEffect)
            {
                texturedNoEffect.World = world;
                texturedNoEffect.Projection = Camera.Projection;
                texturedNoEffect.View = Camera.View;

                texturedNoEffect.Device = graphicsDevice;
                texturedNoEffect.Apply();
            }
        }
    }
}
