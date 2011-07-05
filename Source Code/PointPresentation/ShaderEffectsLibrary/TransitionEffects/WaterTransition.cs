using System;
using System.Windows;
using System.Windows.Media;
using System.Windows.Media.Effects;

namespace ShaderEffectsLibrary
{
    public class WaterTransition : CloudyTransition
    {
        private static PixelShader pixelShader = new PixelShader();

        static WaterTransition()
        {
            pixelShader.UriSource = Global.MakePackUri( "TransitionEffects/Source/WaterTransition.ps" );
        }

        public WaterTransition()
        {
            this.PixelShader = pixelShader;
            this.Name = "Water";
        }
    }
}
