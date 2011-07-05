using System;
using System.Windows;
using System.Windows.Media;
using System.Windows.Media.Effects;

namespace ShaderEffectsLibrary
{
    public class CrumbleTransition : CloudyTransition
    {
        private static PixelShader pixelShader = new PixelShader();

        static CrumbleTransition()
        {
            pixelShader.UriSource = Global.MakePackUri( "TransitionEffects/Source/CrumbleTransition.ps" );
        }

        public CrumbleTransition()
        {
            this.PixelShader = pixelShader;
            this.Name = "Crumble";
        }
    }
}
