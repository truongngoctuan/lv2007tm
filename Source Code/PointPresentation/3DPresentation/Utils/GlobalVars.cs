using Microsoft.Xna.Framework;

namespace _3DPresentation
{
    public class GlobalVars
    {
        public static Color Red = Color.FromNonPremultiplied(255, 0, 0, 255);
        public static Color Green = Color.FromNonPremultiplied(0, 255, 0, 255);
        public static Color Blue = Color.FromNonPremultiplied(0, 0, 255, 255);
        public static Color Orange = Color.FromNonPremultiplied(255, 128, 0, 255);
        public static Color Yellow = Color.FromNonPremultiplied(255, 255, 0, 255);
        public static Color Purple = Color.FromNonPremultiplied(128, 0, 255, 255);
        public static Color Black = Color.FromNonPremultiplied(0, 0, 0, 255);
        public static Color White = Color.FromNonPremultiplied(255, 255, 255, 255);
        public static Color Cyan = Color.FromNonPremultiplied(0, 255, 255, 255);

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
