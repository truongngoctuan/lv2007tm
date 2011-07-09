using Babylon.Toolbox;
using System.Collections.Generic;
using Microsoft.Xna.Framework.Graphics;
using Microsoft.Xna.Framework.Silverlight;

namespace _3DPresentation.Effects
{
    public class EffectManager
    {
        public enum ShaderEffects { NoEffect, TexturedNoEffect, PointEffect }
        // the device to use when creating resources
        static readonly GraphicsDevice resourceDevice = GraphicsDeviceManager.Current.GraphicsDevice;

        public static NoEffect NoEffect { get; private set; }
        public static TexturedNoEffect TexturedNoEffect { get; private set; }
        public static PointEffect PointEffect { get; private set; }

        public static bool IsReady { get; set; }
        public static void InitEffects()
        {
            if (IsReady)
                return;

            NoEffect = new NoEffect(resourceDevice);
            TexturedNoEffect = new TexturedNoEffect(resourceDevice);
            PointEffect = new PointEffect(resourceDevice);

            TexturedNoEffect.DiffuseTexture = Utils.Global.LoadTexture("Images/3.jpg", resourceDevice);

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
