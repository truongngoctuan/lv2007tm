using Babylon.Maths;
using Microsoft.Xna.Framework;
using Microsoft.Xna.Framework.Graphics;
using System;

namespace Babylon
{
    public partial class Scene
    {
        public int RenderedVerticesCount { get; private set; }
        public int RenderedFacesCount { get; private set; }
        public long RenderID { get; private set; }

        //nhminh
        //public void Render()
        public virtual void Render()
        {
            lock (this)
            {
                if (ActiveCamera == null)
                    throw new NullReferenceException(Strings.NoActiveCamera);

                RenderedVerticesCount = 0;
                RenderedFacesCount = 0;
                RenderID++;

                engine.Device.Clear(((AutoClear || ForceWireframe) ? ClearOptions.Target : 0) | ClearOptions.DepthBuffer, ClearColor, 1.0f, 0);

                SelectVisibleWorld();

                // Scene datas
                Engine.StandardEffect.Prepare(this);
                Engine.PerPixelEffect.Prepare(this);

                // Standards
                Engine.StatesManager.DepthBufferWrite = true;
                Engine.Device.BlendState = BlendState.Opaque;
                foreach (SubModel subModel in standardSubModels)
                {
                    subModel.Material.Render(subModel);
                }

                // Opacity                
                Engine.AlphaTestEnable = true;
                foreach (SubModel subModel in opacitySubModels)
                {
                    subModel.Material.Render(subModel);
                }
                Engine.AlphaTestEnable = false;

                // Alpha
                Engine.StatesManager.DepthBufferWrite = false;
                Engine.Device.BlendState = BlendState.NonPremultiplied;
                foreach (SubModel subModel in alphaSubModels)
                {
                    subModel.Material.Render(subModel);
                }

                // Input
                controlManager.MoveCamera();
            }
        }
    }
}

