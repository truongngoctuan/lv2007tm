using System;
using System.Windows;
using System.Windows.Media;
using System.Windows.Media.Effects;

namespace ShaderEffectsLibrary
{
    public class SwirlGridTransition : TransitionEffect
    {
        private static PixelShader pixelShader = new PixelShader();

        public static readonly DependencyProperty TwistAmountProperty =
            DependencyProperty.Register( "TwistAmount", typeof( double ), typeof( SwirlGridTransition ),
                new PropertyMetadata( Math.PI, PixelShaderConstantCallback( 1 ) ) );

        static SwirlGridTransition()
        {
            pixelShader.UriSource = Global.MakePackUri( "TransitionEffects/Source/SwirlGridTransition.ps" );
        }

        public SwirlGridTransition( double twist ) :
            this()
        {
            this.TwistAmount = twist;
        }

        public SwirlGridTransition()
        {
            this.PixelShader = pixelShader;

            this.UpdateShaderValue( TwistAmountProperty );
            this.Name = "Swirl Grid";
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
