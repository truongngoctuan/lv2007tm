using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Windows;

namespace ShaderEffectsLibrary
{
    public abstract class RandomTransition : TransitionEffect
    {
        public static readonly DependencyProperty RandomSeedProperty =
            DependencyProperty.Register( "RandomSeed", typeof( double ), typeof( RandomTransition ),
                new PropertyMetadata( 0.0, PixelShaderConstantCallback( 1 ) ) );

        protected RandomTransition()
        {
            this.UpdateShaderValue( RandomSeedProperty );
        }

        public double RandomSeed
        {
            get
            {
                return ( double ) this.GetValue( RandomSeedProperty );
            }
            set
            {
                this.SetValue( RandomSeedProperty, value );
            }
        }
    }
}
