using System;
using System.Windows;
using System.Windows.Media;
using System.Windows.Media.Effects;

namespace ShaderEffectsLibrary
{
    public class SmoothSwirlGridTransition : TransitionEffect
    {
        private static PixelShader pixelShader = new PixelShader();

        public static readonly DependencyProperty TwistAmountProperty =
            DependencyProperty.Register( "TwistAmount", typeof( double ),
                typeof( SmoothSwirlGridTransition ),
                new PropertyMetadata( Math.PI, PixelShaderConstantCallback( 1 ) ) );

        static SmoothSwirlGridTransition()
        {
            pixelShader.UriSource = Global.MakePackUri( "TransitionEffects/Source/SmoothSwirlGridTransition.ps" );
        }

        public SmoothSwirlGridTransition( double twist ) :
            this()
        {
            this.TwistAmount = twist;
        }

        public SmoothSwirlGridTransition()
        {
            this.PixelShader = pixelShader;
            this.UpdateShaderValue( TwistAmountProperty );
            this.Name = "Smooth Swirl Grid";
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
