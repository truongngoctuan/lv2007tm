using System;
using System.Windows;
using System.Windows.Media;
using System.Windows.Media.Effects;

namespace ShaderEffectsLibrary
{
    public class PixelateOutTransition : TransitionEffect
    {
        private static PixelShader pixelShader = new PixelShader();

        static PixelateOutTransition()
        {
            pixelShader.UriSource = Global.MakePackUri( "TransitionEffects/Source/PixelateOutTransition.ps" );
        }

        public PixelateOutTransition()
        {
            this.PixelShader = pixelShader;
            this.Name = "Pixelate Out";
        }
    }
}
