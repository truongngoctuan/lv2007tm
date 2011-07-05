using System;
using System.Windows;
using System.Windows.Media;
using System.Windows.Media.Effects;

namespace ShaderEffectsLibrary
{
    public class CloudRevealTransition : CloudyTransition
    {
        private static PixelShader pixelShader = new PixelShader();

        static CloudRevealTransition()
        {
            pixelShader.UriSource = Global.MakePackUri( "TransitionEffects/Source/CloudRevealTransition.ps" );
        }

        public CloudRevealTransition()
        {
            this.PixelShader = pixelShader;
            this.Name = "Cloud Reveal";
        }
    }
}
