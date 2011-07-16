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
        public virtual void RenderExtendedStandardModel()
        { 
        }

        public virtual void RenderExtendedOpacityModel()
        {
        }

        public virtual void RenderExtendedAlphaModel()
        {
        }

        public static bool bStandardModel = true;
        public static bool bOpacityModel = true;
        public static bool bAlphaModel = true;

        public virtual void Render()
        {
            lock (this)
            {
                if (ActiveCamera == null)
                    throw new NullReferenceException(Strings.NoActiveCamera);

                RenderedVerticesCount = 0;
                RenderedFacesCount = 0;
                RenderID++;

                AutoClear = true;
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
                    if(bStandardModel)
                    subModel.Material.Render(subModel);
                }
                //nhminh
                RenderExtendedStandardModel();

                // Opacity                
                Engine.AlphaTestEnable = true;
                foreach (SubModel subModel in opacitySubModels)
                {
                    if (bOpacityModel)
                    subModel.Material.Render(subModel);
                }
                //nhminh
                RenderExtendedOpacityModel();
                Engine.AlphaTestEnable = false;                

                // Alpha
                Engine.StatesManager.DepthBufferWrite = false;
                Engine.Device.BlendState = BlendState.NonPremultiplied;
                foreach (SubModel subModel in alphaSubModels)
                {
                    if (bAlphaModel)
                    subModel.Material.Render(subModel);
                }
                //nhminh
                RenderExtendedAlphaModel();

                // Input
                controlManager.MoveCamera();
            }
        }
    }
}

