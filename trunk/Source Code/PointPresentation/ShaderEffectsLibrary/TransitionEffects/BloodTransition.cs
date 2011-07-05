using System;
using System.Windows;
using System.Windows.Media;
using System.Windows.Media.Effects;

namespace ShaderEffectsLibrary
{
    public class BloodTransition : CloudyTransition
    {
        private static PixelShader pixelShader = new PixelShader();

        static BloodTransition()
        {
            pixelShader.UriSource = Global.MakePackUri( "TransitionEffects/Source/BloodTransition.ps" );
        }

        public BloodTransition()
        {
            this.PixelShader = pixelShader;
            this.Name = "Blood";
        }
    }
}
