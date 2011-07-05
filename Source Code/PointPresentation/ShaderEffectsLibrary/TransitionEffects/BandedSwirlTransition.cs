using System;
using System.Windows;
using System.Windows.Media;
using System.Windows.Media.Effects;

namespace ShaderEffectsLibrary
{
    public class BandedSwirlTransition : TransitionEffect
    {
        private static PixelShader pixelShader = new PixelShader();

        public static readonly DependencyProperty TwistAmountProperty =
            DependencyProperty.Register( "TwistAmount", typeof( double ),
                typeof( BandedSwirlTransition ), 
                new PropertyMetadata( Math.PI / 4.0, PixelShaderConstantCallback( 1 ) ) );

        public static readonly DependencyProperty FrequencyProperty =
            DependencyProperty.Register( "Frequency", typeof( double ),
                typeof( BandedSwirlTransition ), 
                new PropertyMetadata( 50.0, PixelShaderConstantCallback( 2 ) ) );


        static BandedSwirlTransition()
        {
            pixelShader.UriSource = Global.MakePackUri( "TransitionEffects/Source/BandedSwirlTransition.ps" );
        }

        public BandedSwirlTransition( double twist, double frequency ) :
            this()
        {
            this.TwistAmount = twist;
            this.Frequency = frequency;
        }

        public BandedSwirlTransition()
        {
            this.PixelShader = pixelShader;

            this.UpdateShaderValue( TwistAmountProperty );
            this.UpdateShaderValue( FrequencyProperty );
            this.Name = "Banded Swirl";
        }

        public double TwistAmount
        {
            get
            {
                return ( double ) this.GetValue( TwistAmountProperty );
            }
            set
            {
                this.SetValue( TwistAmountProperty, value );
            }
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
