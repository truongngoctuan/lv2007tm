using System;
using System.Windows;
using System.Windows.Media;
using System.Windows.Media.Effects;

namespace ShaderEffectsLibrary
{
    public class CircleStrechTransition : TransitionEffect
    {
        private static PixelShader pixelShader = new PixelShader();

        static CircleStrechTransition()
        {
            pixelShader.UriSource = Global.MakePackUri( "TransitionEffects/Source/CircleStrechTransition.ps" );
        }

        public CircleStrechTransition()
        {
            this.PixelShader = pixelShader;
            this.Name = "Circle Strech";
        }
    }
}
