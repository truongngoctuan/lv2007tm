using System;
using System.Windows;
using System.Windows.Media;
using System.Windows.Media.Effects;

namespace ShaderEffectsLibrary
{
    public class FadeTransition : TransitionEffect
    {
        private static PixelShader pixelShader = new PixelShader();

        static FadeTransition()
        {
            pixelShader.UriSource = Global.MakePackUri( "TransitionEffects/Source/FadeTransition.ps" );
        }

        public FadeTransition()
        {
            this.PixelShader = pixelShader;
            this.Name = "Fade";
        }
    }
}
