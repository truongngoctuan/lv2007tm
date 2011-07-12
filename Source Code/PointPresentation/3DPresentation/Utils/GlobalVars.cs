using Microsoft.Xna.Framework;
using Microsoft.Xna.Framework.Silverlight;
using Microsoft.Xna.Framework.Graphics;

namespace _3DPresentation
{
    public class GlobalVars
    {
        // the device to use when creating resources
        public static readonly GraphicsDevice resourceDevice = GraphicsDeviceManager.Current.GraphicsDevice;

        public enum ColorEnum { Transparent, Red, Green, Blue, Orange, Yellow, Purple, Black, White, Cyan }
        public static Color GetColor(ColorEnum color)
        {
            switch (color)
            {
                case ColorEnum.White:
                    return Color.FromNonPremultiplied(255, 255, 255, 255);
                case ColorEnum.Black:
                    return Color.FromNonPremultiplied(0, 0, 0, 255);
                case ColorEnum.Red:
                    return Color.FromNonPremultiplied(255, 0, 0, 255);
                case ColorEnum.Green:
                    return Color.FromNonPremultiplied(0, 255, 0, 255);
                case ColorEnum.Blue:
                    return Color.FromNonPremultiplied(0, 0, 255, 255);
                case ColorEnum.Orange:
                    return Color.FromNonPremultiplied(255, 128, 0, 255);
                case ColorEnum.Yellow:
                    return Color.FromNonPremultiplied(255, 255, 0, 255);
                case ColorEnum.Purple:
                    return Color.FromNonPremultiplied(128, 0, 255, 255);
                case ColorEnum.Cyan:
                    return Color.FromNonPremultiplied(0, 255, 255, 255);
                default:
                    return Color.Transparent;
            }
        }

        public enum ShaderEffect { NoEffect, MyBasicEffect, BasicEffect, PointEffect, FourPointLights };
        public enum LOD { LOW = 5, MEDIUM = 3, HIGH = 1 };
        public static LOD LevelOfDetail = LOD.LOW;

        public static Vector3 Light1 { get; set; }
        public static Vector3 Light2 { get; set; }
        public static Vector3 Light3 { get; set; }
        public static Vector3 Light4 { get; set; }

        public static Vector4 EnableLights { get; set; }
    }
}
