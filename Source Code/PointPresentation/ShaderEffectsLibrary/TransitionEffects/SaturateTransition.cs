using System;
using System.Windows;
using System.Windows.Media;
using System.Windows.Media.Effects;

namespace ShaderEffectsLibrary
{
    public class SaturateTransition : TransitionEffect
    {
        private static PixelShader pixelShader = new PixelShader();

        static SaturateTransition()
        {
            pixelShader.UriSource = Global.MakePackUri( "TransitionEffects/Source/SaturateTransition.ps" );
        }

        public SaturateTransition()
        {
            this.PixelShader = pixelShader;
            this.Name = "Saturate";
        }
    }
}
