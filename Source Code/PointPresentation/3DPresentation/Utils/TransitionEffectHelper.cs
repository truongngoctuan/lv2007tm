using System;
using System.Windows;
using System.Windows.Controls;
using System.Windows.Media.Imaging;
using ShaderEffectsLibrary;


namespace _3DPresentation.Utils
{
    public class TransitionEffectHelper
    {
        static TransitionEffect transitionEffect = new ShaderEffectsLibrary.WaterTransition();
        public static void BeginAnimation(UserControl oldControl, UserControl newControl)
        {                
            WriteableBitmap capture = new WriteableBitmap(oldControl, new System.Windows.Media.ScaleTransform());
            System.Windows.Media.ImageBrush imageBrush = new System.Windows.Media.ImageBrush();
            imageBrush.ImageSource = capture;
            transitionEffect.OldImage = imageBrush;

            newControl.Effect = transitionEffect;

            #region WPF ShaderEffect Animation
            /*
            DoubleAnimation da = new DoubleAnimation();
            da.From = 0;
            da.To = 1;
            da.Duration = TimeSpan.FromSeconds(3);
            //da.AutoReverse = true;
            //da.RepeatBehavior = RepeatBehavior.Forever;
            transitionEffect.BeginAnimation(TransitionEffect.ProgressProperty, da);
             * */
            #endregion

            #region Silverlight ShaderEffect Animation

            System.Windows.Media.Animation.DoubleAnimation da = new System.Windows.Media.Animation.DoubleAnimation();
            da.From = 0;
            da.To = 1;
            da.Duration = TimeSpan.FromSeconds(3);
            da.AutoReverse = false;
            //da.RepeatBehavior = System.Windows.Media.Animation.RepeatBehavior.Forever;

            //Storyboard st = (LayoutRoot.Resources)["st"] as Storyboard;
            System.Windows.Media.Animation.Storyboard st = new System.Windows.Media.Animation.Storyboard();
            System.Windows.Media.Animation.Storyboard.SetTarget(da, transitionEffect);
            System.Windows.Media.Animation.Storyboard.SetTargetProperty(da, new PropertyPath(TransitionEffect.ProgressProperty));
            st.Children.Add(da);
            st.Completed += new EventHandler(delegate 
                {
                    newControl.Effect = null;
                });
            st.Begin();

            #endregion
        }
    }
}
