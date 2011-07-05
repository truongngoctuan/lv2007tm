using System;
using System.Windows;
using System.Windows.Media;
using System.Windows.Media.Effects;

namespace ShaderEffectsLibrary
{
    public class SwirlTransition : TransitionEffect
    {
        private static PixelShader pixelShader = new PixelShader();

        public static readonly DependencyProperty TwistAmountProperty = 
            DependencyProperty.Register( "TwistAmount", typeof( double ),
                typeof( SwirlTransition ), 
                new PropertyMetadata( Math.PI, PixelShaderConstantCallback( 1 ) ) );

        static SwirlTransition()
        {
            pixelShader.UriSource = Global.MakePackUri( "TransitionEffects/Source/SwirlTransition.ps" );
        }

        public SwirlTransition()
        {
            this.PixelShader = pixelShader;
            this.UpdateShaderValue( TwistAmountProperty );
            this.Name = "Swirl";
        }

        public SwirlTransition( double twist )
            : this()
        {
            this.TwistAmount = twist;
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
    }
}
