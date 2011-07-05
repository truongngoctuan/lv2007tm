using System;
using System.Windows;
using System.Windows.Media;
using System.Windows.Media.Effects;

namespace ShaderEffectsLibrary
{
    public class PixelateInTransition : TransitionEffect
    {
        private static PixelShader pixelShader = new PixelShader();

        static PixelateInTransition()
        {
            pixelShader.UriSource = Global.MakePackUri( "TransitionEffects/Source/PixelateInTransition.ps" );
        }

        public PixelateInTransition()
        {
            this.PixelShader = pixelShader;
            this.Name = "Pixelate In";
        }
    }
}
