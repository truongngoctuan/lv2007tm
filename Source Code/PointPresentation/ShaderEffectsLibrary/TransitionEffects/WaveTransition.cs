using System;
using System.Windows;
using System.Windows.Media;
using System.Windows.Media.Effects;

namespace ShaderEffectsLibrary
{
    public class WaveTransition : TransitionEffect
    {
        private static PixelShader pixelShader = new PixelShader();

        static WaveTransition()
        {
            pixelShader.UriSource = Global.MakePackUri( "TransitionEffects/Source/WaveTransition.ps" );
        }

        public WaveTransition()
        {
            this.PixelShader = pixelShader;
            this.Name = "Wave";
        }
    }
}
