using System;
using System.Windows;
using System.Windows.Media;
using System.Windows.Media.Effects;
using System.Windows.Media.Imaging;

namespace ShaderEffectsLibrary
{
    public class DissolveTransition : RandomTransition
    {
        private static PixelShader pixelShader = new PixelShader();

        public static readonly DependencyProperty NoiseImageProperty =
                ShaderEffect.RegisterPixelShaderSamplerProperty( "NoiseImage",
                    typeof( DissolveTransition ), 2, SamplingMode.Bilinear );


        static DissolveTransition()
        {
            pixelShader.UriSource = Global.MakePackUri( "TransitionEffects/Source/DissolveTransition.ps" );
        }

        public DissolveTransition()
        {
            this.PixelShader = pixelShader;

            ImageBrush imageBrush = new ImageBrush();
            imageBrush.ImageSource = new BitmapImage( Global.MakePackUri( "TransitionImages/noise.png" ) );
            this.NoiseImage = imageBrush;
            this.UpdateShaderValue( NoiseImageProperty );
            this.Name = "Dissolve";
        }

        protected Brush NoiseImage
        {
            get
            {
                return this.GetValue( NoiseImageProperty ) as Brush;
            }
            set
            {
                this.SetValue( NoiseImageProperty, value );
            }
        }
    }
}
