using System;
using System.Windows.Media.Effects;
using System.Windows;

namespace NavigationWithTransitions
{
  public class ReflectionShader : ShaderEffect
  {
    static PropertyChangedCallback ElementHeightRegisterCallback;

    static ReflectionShader()
    {
      ElementHeightRegisterCallback = ShaderEffect.PixelShaderConstantCallback(1);
    }

    public ReflectionShader()
    {
        //Uri u = new Uri(@"/NavigationWithTransitions;component/Reflection.ps", UriKind.Relative);
        Uri u = new Uri(@"/NavigationWithTransitions;component/Reflection.ps", UriKind.Relative);
      PixelShader = new PixelShader() { UriSource = u };
      base.UpdateShaderValue(ElementHeightProperty);
    }

    public static readonly DependencyProperty ElementHeightProperty =
            DependencyProperty.Register("ElementHeight",
            typeof(double),
            typeof(ReflectionShader),
            new PropertyMetadata(100.0, OnElementHeightChanged));

    static void OnElementHeightChanged(DependencyObject d, 
      DependencyPropertyChangedEventArgs e)
    {
      ElementHeightRegisterCallback(d, e);
      (d as ReflectionShader).OnElementHeightChanged(
        (double)e.OldValue, 
        (double)e.NewValue);
    }

    protected virtual void OnElementHeightChanged(double oldValue, double newValue)
    {
      PaddingBottom = newValue;
    }

    public double ElementHeight
    {
      get { return (double)base.GetValue(ElementHeightProperty); }
      set { base.SetValue(ElementHeightProperty, value); }
    }
  }
}