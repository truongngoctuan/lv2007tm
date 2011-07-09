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

        // Effects
        private enum ShaderEffect { NoEffect, TexturedNoEffect };
        NoEffect noEffect;
        TexturedNoEffect texturedNoEffect;

        private void PrepareRender()
        {
            noEffect = new NoEffect(Device);
            texturedNoEffect = new TexturedNoEffect(Device);

            Surface.Dispatcher.BeginInvoke(() =>
            {
                texturedNoEffect.DiffuseTexture = Utils.Global.LoadTexture("Images/3.jpg", Device);
            });
        }

        public override void Render()
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

            foreach (FaceModel faceModel in customSceneModels)
            {
                if (faceModel.IsEnabled)
                {
                    if (ActiveCamera.IsInFrustrum(faceModel.BoundingInfo))
                    {
                        if (faceModel == selectedMesh)
                            SetShaderEffect(ShaderEffect.TexturedNoEffect, faceModel.WorldMatrix);
                        else
                            SetShaderEffect(ShaderEffect.NoEffect, faceModel.WorldMatrix);
                        faceModel.Render(Device);
                    }
                    //break;
                }
            }

            if(Drawed != null)
                Drawed(this, EventArgs.Empty);
        }

        private void SetShaderEffect(ShaderEffect shaderEffect, Matrix world)
        {
            if (shaderEffect == ShaderEffect.NoEffect)
            {
                noEffect.World = world;
                noEffect.Projection = ActiveCamera.Projection;
                noEffect.View = ActiveCamera.View;

                noEffect.Device = Device;
                noEffect.Apply();
            }
            else if (shaderEffect == ShaderEffect.TexturedNoEffect)
            {
                texturedNoEffect.World = world;
                texturedNoEffect.Projection = ActiveCamera.Projection;
                texturedNoEffect.View = ActiveCamera.View;

                texturedNoEffect.Device = Device;
                texturedNoEffect.Apply();
            }
        }
    }
}
