using System;
using System.Windows;
using System.Windows.Media;
using System.Windows.Media.Effects;

namespace ShaderEffectsLibrary
{
    public class ShrinkTransition : TransitionEffect
    {
        private static PixelShader pixelShader = new PixelShader();

        static ShrinkTransition()
        {
            pixelShader.UriSource = Global.MakePackUri( "TransitionEffects/Source/ShrinkTransition.ps" );
        }

        public ShrinkTransition()
        {
            this.PixelShader = pixelShader;
            this.Name = "Shrink";
        }
    }
}
