using System;
using System.Windows;
using System.Windows.Media;
using System.Windows.Media.Effects;

namespace ShaderEffectsLibrary
{
    public class LeastBrightTransition : TransitionEffect
    {
        private static PixelShader pixelShader = new PixelShader();

        static LeastBrightTransition()
        {
            pixelShader.UriSource = Global.MakePackUri( "TransitionEffects/Source/LeastBrightTransition.ps" );
        }

        public LeastBrightTransition()
        {
            this.PixelShader = pixelShader;
            this.Name = "Least Bright";
        }
    }
}
