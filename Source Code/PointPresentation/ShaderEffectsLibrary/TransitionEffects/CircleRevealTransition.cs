using System;
using System.Windows;
using System.Windows.Media;
using System.Windows.Media.Effects;

namespace ShaderEffectsLibrary
{
    public class CircleRevealTransition : TransitionEffect
    {
        private static PixelShader pixelShader = new PixelShader();

        public static readonly DependencyProperty FuzzyAmountProperty = 
            DependencyProperty.Register( "FuzzyAmount", typeof( double ),
                typeof( CircleRevealTransition ), 
                new PropertyMetadata( 0.1, PixelShaderConstantCallback( 1 ) ) );


        static CircleRevealTransition()
        {
            pixelShader.UriSource = Global.MakePackUri( "TransitionEffects/Source/CircleRevealTransition.ps" );
        }

        public CircleRevealTransition()
        {
            this.PixelShader = pixelShader;
            this.UpdateShaderValue( FuzzyAmountProperty );
            this.Name = "Circle Reveal";
        }

        public CircleRevealTransition( double fuzzyAmount ) :
            this()
        {
            this.FuzzyAmount = fuzzyAmount;
        }

        public double FuzzyAmount
        {
            get
            {
                return ( double ) this.GetValue( FuzzyAmountProperty );
            }
            set
            {
                this.SetValue( FuzzyAmountProperty, value );
            }
        }
    }
}
