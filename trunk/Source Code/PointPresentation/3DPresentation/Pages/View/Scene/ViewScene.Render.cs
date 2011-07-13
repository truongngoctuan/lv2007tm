﻿using _3DPresentation.Effects;
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
                graphicsDevice.Clear(ClearOptions.Target | ClearOptions.DepthBuffer, Color.Transparent, 1.0f, 0);
                graphicsDevice.RasterizerState = new RasterizerState
                {
                    FillMode = FillMode.Solid,
                    CullMode = CullMode.None
                };

                BaseModel[] models;
                lock (lockThis)
                {
                    models = Models.ToArray();
                }
                foreach (BaseModel model in models)
                {
                    if (model.IsEnabled)
                    {
                        model.Render(graphicsDevice);
                    }
                }
                
                models = null;
            }
            catch (ArgumentException ex)
            {
                DrawError++;
            }
        }
    }
}
