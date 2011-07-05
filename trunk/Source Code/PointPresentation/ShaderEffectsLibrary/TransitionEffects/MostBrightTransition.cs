using System;
using System.Windows;
using System.Windows.Media;
using System.Windows.Media.Effects;

namespace ShaderEffectsLibrary
{
    public class MostBrightTransition : TransitionEffect
    {
        private static PixelShader pixelShader = new PixelShader();

        static MostBrightTransition()
        {
            pixelShader.UriSource = Global.MakePackUri( "TransitionEffects/Source/MostBrightTransition.ps" );
        }

        public MostBrightTransition()
        {
            this.PixelShader = pixelShader;
            this.Name = "Most Bright";
        }
    }
}
