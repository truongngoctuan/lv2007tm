using System;
using System.Windows;
using System.Windows.Media;
using System.Windows.Media.Effects;

namespace ShaderEffectsLibrary
{
    public class BlindsTransition : TransitionEffect
    {
         private static PixelShader pixelShader = new PixelShader();

        static BlindsTransition()
        {
            pixelShader.UriSource = Global.MakePackUri( "TransitionEffects/Source/BlindsTransition.ps" );
        }

        public BlindsTransition()
        {
            this.PixelShader = pixelShader;
            this.Name = "Blinds";
        }
    }
}
