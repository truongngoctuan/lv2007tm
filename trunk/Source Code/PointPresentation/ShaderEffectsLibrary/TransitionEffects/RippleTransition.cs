using System;
using System.Windows;
using System.Windows.Media;
using System.Windows.Media.Effects;

namespace ShaderEffectsLibrary
{
    public class RippleTransition : TransitionEffect
    {
        private static PixelShader pixelShader = new PixelShader();

        public static readonly DependencyProperty FrequencyProperty = 
            DependencyProperty.Register( "Frequency", typeof( double ),
                typeof( RippleTransition ), 
                new PropertyMetadata( 20.0, PixelShaderConstantCallback( 1 ) ) );

        static RippleTransition()
        {
            pixelShader.UriSource = Global.MakePackUri( "TransitionEffects/Source/RippleTransition.ps" );
        }

        public RippleTransition()
        {
            this.PixelShader = pixelShader;
            this.UpdateShaderValue( FrequencyProperty );
            this.Name = "Ripple";
        }

        public RippleTransition( double frequency ) :
            this()
        {
            this.Frequency = frequency;
        }

        public double Frequency
        {
            get
            {
                return ( double ) this.GetValue( FrequencyProperty );
            }
            set
            {
                this.SetValue( FrequencyProperty, value );
            }
        }
    }
}
