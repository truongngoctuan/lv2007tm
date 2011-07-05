using System;
using System.Windows;
using System.Windows.Media;
using System.Windows.Media.Effects;

namespace ShaderEffectsLibrary
{
    public class RandomCircleRevealTransition : CloudyTransition
    {
        private static PixelShader pixelShader = new PixelShader();

        static RandomCircleRevealTransition()
        {
            pixelShader.UriSource = Global.MakePackUri( "TransitionEffects/Source/RandomCircleRevealTransition.ps" );
        }

        public RandomCircleRevealTransition()
        {
            this.PixelShader = pixelShader;
            this.Name = "Random Circle Reveal";
        }

    }
}
