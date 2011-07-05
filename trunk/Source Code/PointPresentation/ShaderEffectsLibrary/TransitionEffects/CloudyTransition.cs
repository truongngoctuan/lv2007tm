using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Windows;
using System.Windows.Media.Effects;
using System.Windows.Media;
using System.Windows.Media.Imaging;

namespace ShaderEffectsLibrary
{
    public abstract class CloudyTransition : RandomTransition
    {
        public static readonly DependencyProperty CloudImageProperty =
            ShaderEffect.RegisterPixelShaderSamplerProperty( "CloudImage", typeof( CloudyTransition ),
                2, SamplingMode.Bilinear );

        protected CloudyTransition()
        {
            ImageBrush imageBrush = new ImageBrush();
            imageBrush.ImageSource = new BitmapImage( Global.MakePackUri( "TransitionImages/Clouds.png" ) );
            this.CloudImage = imageBrush;
            this.UpdateShaderValue( CloudImageProperty );
        }

        public Brush CloudImage
        {
            get
            {
                return this.GetValue( CloudImageProperty ) as Brush;
            }
            set
            {
                this.SetValue( CloudImageProperty, value );
            }
        }
    }
}
