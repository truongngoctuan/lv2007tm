using Babylon.Toolbox;
using System.Collections.Generic;
using Microsoft.Xna.Framework.Graphics;
using Microsoft.Xna.Framework.Silverlight;

namespace _3DPresentation.Effects
{
    public class EffectManager
    {
        public enum ShaderEffects { NoEffect, TexturedNoEffect, PointEffect }
        // the device to use when creating resources, can't use to draw
        static readonly GraphicsDevice resourceDevice = GraphicsDeviceManager.Current.GraphicsDevice;

        public static IBaseScene Scene { get; set; }
        public static NoEffect noEffect;
        public static TexturedNoEffect texturedNoEffect;
        public static PointEffect pointEffect;

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

        public static bool IsReady { get; set; }
        public static void InitEffects()
        {
            if (IsReady)
                return;

            noEffect = new NoEffect(resourceDevice);

            texturedNoEffect = new TexturedNoEffect(resourceDevice);
            texturedNoEffect.DiffuseTexture = Utils.Global.LoadTexture("Images/3.jpg", resourceDevice);

            pointEffect = new PointEffect(resourceDevice);
            IsReady = true;
        }

        public static Effect GetEffect(ShaderEffects effect)
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
