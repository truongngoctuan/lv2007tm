using System;
using System.Windows;
using System.Windows.Media;
using System.Windows.Media.Effects;

namespace ShaderEffectsLibrary
{
    public class RadialWiggleTransition : CloudyTransition
    {
        private static PixelShader pixelShader = new PixelShader();

        static RadialWiggleTransition()
        {
            pixelShader.UriSource = Global.MakePackUri( "TransitionEffects/Source/RadialWiggleTransition.ps" );
        }

        public RadialWiggleTransition()
        {
            this.PixelShader = pixelShader;
            this.Name = "Radial Wiggle";
        }
    }
}
