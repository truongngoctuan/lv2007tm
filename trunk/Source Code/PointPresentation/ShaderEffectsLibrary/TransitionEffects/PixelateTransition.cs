using System;
using System.Windows;
using System.Windows.Media;
using System.Windows.Media.Effects;

namespace ShaderEffectsLibrary
{
    public class PixelateTransition : TransitionEffect
    {
        private static PixelShader pixelShader = new PixelShader();

        static PixelateTransition()
        {
            pixelShader.UriSource = Global.MakePackUri( "TransitionEffects/Source/PixelateTransition.ps" );
        }

        public PixelateTransition()
        {
            this.PixelShader = pixelShader;
            this.Name = "Pixelate";
        }
    }
}
