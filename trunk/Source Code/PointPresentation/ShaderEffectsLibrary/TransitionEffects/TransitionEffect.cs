using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Windows;
using System.Windows.Media.Effects;
using System.Windows.Media;

namespace ShaderEffectsLibrary
{
    public abstract class TransitionEffect : ShaderEffectBase
    {
        /// <summary>
        /// Dependency property for the old image.
        /// </summary>
        public static readonly DependencyProperty OldImageProperty =
            ShaderEffect.RegisterPixelShaderSamplerProperty( "OldImage", typeof( TransitionEffect ), 1, SamplingMode.NearestNeighbor );

        /// <summary>
        /// Dependency property for the transition progress.
        /// </summary>
        public static readonly DependencyProperty ProgressProperty =
            DependencyProperty.Register( "Progress", typeof( double ), typeof( TransitionEffect ),
                new PropertyMetadata( 0.0, PixelShaderConstantCallback( 0 ) ) );

        protected TransitionEffect()
        {
            this.UpdateShaderValue( OldImageProperty );
            this.UpdateShaderValue( ProgressProperty );
        }

        /// <summary>
        /// Gets, sets the old image used in the transition animation.
        /// </summary>
        public Brush OldImage
        {
            get
            {
                return this.GetValue( OldImageProperty ) as Brush;
            }
            set
            {
                this.SetValue( OldImageProperty, value );
            }
        }

        /// <summary>
        /// Gets, sets the progress of the transition animation.
        /// </summary>
        public double Progress
        {
            get
            {
                return ( double ) this.GetValue( ProgressProperty );
            }
            set
            {
                this.SetValue( ProgressProperty, value );
            }
        }
    }
}
