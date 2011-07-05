using System;
using System.Windows;
using System.Windows.Media;
using System.Windows.Media.Effects;

namespace ShaderEffectsLibrary
{
    public class RotateCrumbleTransition : CloudyTransition
    {
        private static PixelShader pixelShader = new PixelShader();

        static RotateCrumbleTransition()
        {
            pixelShader.UriSource = Global.MakePackUri( "TransitionEffects/Source/RotateCrumbleTransition.ps" );
        }

        public RotateCrumbleTransition()
        {
            this.PixelShader = pixelShader;
            this.Name = "Rotate Crumble";
        }
    }
}
