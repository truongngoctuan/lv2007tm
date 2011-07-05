using System;
using System.Windows;
using System.Windows.Media;
using System.Windows.Media.Effects;

namespace ShaderEffectsLibrary
{
    public class DropFadeTransition : CloudyTransition
    {
        private static PixelShader pixelShader = new PixelShader();

        static DropFadeTransition()
        {
            pixelShader.UriSource = Global.MakePackUri( "TransitionEffects/Source/DropFadeTransition.ps" );
        }

        public DropFadeTransition()
        {
            this.PixelShader = pixelShader;
            this.Name = "Drop Fade";
        }
    }
}
