using Babylon.Toolbox;
using System.Collections.Generic;
using Microsoft.Xna.Framework.Graphics;
using Microsoft.Xna.Framework.Silverlight;

namespace _3DPresentation.Effects
{
    public class EffectManager
    {
        public enum ShaderEffects { NoEffect, TexturedNoEffect, PointEffect, FourPointLights, VertexColorEffect, BasicEffect, TextureEffect ,FourPointLightsTextureEffect }
        // the device to use when creating resources, can't use to draw
        static readonly GraphicsDevice resourceDevice = GraphicsDeviceManager.Current.GraphicsDevice;

        public static IBaseScene Scene { get; set; }
        private static NoEffect noEffect;
        private static TexturedNoEffect texturedNoEffect;
        private static PointEffect pointEffect;
        private static FourPointLightsEffect fourPointLightsEffect;
        private static VertexColorEffect vertexColorEffect;
        private static BasicEffect basicEffect;
        private static TextureEffect textureEffect;
        private static FourPointLightsTextureEffect fourPointLightsTextureEffect;

        public static NoEffect NoEffect 
        { 
            get 
            {
                if (!IsReady)
                    InitEffects();
                return noEffect; 
            } 
            private set { noEffect = value; } 
        }
        public static TexturedNoEffect TexturedNoEffect
        {
            get 
            {
                if (!IsReady)
                    InitEffects(); 
                return texturedNoEffect;
            }
            private set { texturedNoEffect = value; }
        }
        public static PointEffect PointEffect
        {
            get
            {
                if (!IsReady)
                    InitEffects(); 
                return pointEffect;
            }
            private set { pointEffect = value; }
        }
        public static FourPointLightsEffect FourPointLightsEffect
        {
            get
            {
                if (!IsReady)
                    InitEffects();
                return fourPointLightsEffect;
            }
            private set { fourPointLightsEffect = value; }
        }
        public static VertexColorEffect VertexColorEffect
        {
            get 
            {
                if (!IsReady)
                    InitEffects();
                return vertexColorEffect;
            }
            private set { vertexColorEffect = value; }
        }
        public static BasicEffect BasicEffect
        {
            get
            {
                if (!IsReady)
                    InitEffects();
                return basicEffect;
            }
            private set { basicEffect = value; }
        }
        public static TextureEffect TextureEffect
        {
            get
            {
                if (!IsReady)
                    InitEffects();
                return textureEffect;
            }
            private set { textureEffect = value; }
        }
        public static FourPointLightsTextureEffect FourPointLightsTextureEffect
        {
            get
            {
                if (!IsReady)
                    InitEffects();
                return fourPointLightsTextureEffect;
            }
            private set { fourPointLightsTextureEffect = value; }
        }

        


        public static bool IsReady { get; set; }
        public static void InitEffects()
        {
            if (IsReady)
                return;

            noEffect = new NoEffect(resourceDevice);

            texturedNoEffect = new TexturedNoEffect(resourceDevice);
            texturedNoEffect.DiffuseTexture = ResourceManager.GetTexture("Images/3.jpg");

            pointEffect = new PointEffect(resourceDevice);

            fourPointLightsEffect = new FourPointLightsEffect(resourceDevice);

            vertexColorEffect = new VertexColorEffect(resourceDevice);

            basicEffect = new Babylon.Toolbox.BasicEffect(resourceDevice);

            textureEffect = new TextureEffect(resourceDevice);

            fourPointLightsTextureEffect = new FourPointLightsTextureEffect(resourceDevice);

            IsReady = true;
        }

        private static Effect GetEffect(ShaderEffects effect)
        {
            Effect newEffect = null;
            if (effect == ShaderEffects.NoEffect)
            {
                NoEffect noEffect = new NoEffect(resourceDevice);
                newEffect = noEffect;
            }
            else if (effect == ShaderEffects.TexturedNoEffect)
            {
                TexturedNoEffect texturedNoEffect = new TexturedNoEffect(resourceDevice);
                texturedNoEffect.DiffuseTexture = TexturedNoEffect.DiffuseTexture;
                newEffect = texturedNoEffect;
            }
            else if (effect == ShaderEffects.NoEffect)
            {
                PointEffect pointEffect = new PointEffect(resourceDevice);
                newEffect = pointEffect;
            }
            return newEffect;
        }
    }
}
