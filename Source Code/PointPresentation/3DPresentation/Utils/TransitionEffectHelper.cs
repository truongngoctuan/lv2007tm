using System;
using System.Windows;
using System.Windows.Controls;
using System.Windows.Media.Imaging;
using ShaderEffectsLibrary;


namespace _3DPresentation.Utils
{
    public class TransitionEffectHelper
    {
        private static TransitionEffect[] transitionEffects = null;
        private static bool IsReady = false;
        private static Random r = new Random(DateTime.Now.Millisecond);
        public static void Init()
        {
            transitionEffects = new TransitionEffect[25];
            transitionEffects[0] = new ShaderEffectsLibrary.BandedSwirlTransition();
            transitionEffects[1] = new ShaderEffectsLibrary.BlindsTransition();
            transitionEffects[2] = new ShaderEffectsLibrary.BloodTransition();
            transitionEffects[3] = new ShaderEffectsLibrary.CircleRevealTransition();
            transitionEffects[4] = new ShaderEffectsLibrary.CircleStrechTransition();
            transitionEffects[5] = new ShaderEffectsLibrary.CloudRevealTransition();
            transitionEffects[6] = new ShaderEffectsLibrary.CrumbleTransition();
            transitionEffects[7] = new ShaderEffectsLibrary.DissolveTransition();
            transitionEffects[8] = new ShaderEffectsLibrary.DropFadeTransition();
            transitionEffects[9] = new ShaderEffectsLibrary.FadeTransition();
            transitionEffects[10] = new ShaderEffectsLibrary.LeastBrightTransition();
            transitionEffects[11] = new ShaderEffectsLibrary.MostBrightTransition();
            transitionEffects[12] = new ShaderEffectsLibrary.PixelateInTransition();
            transitionEffects[13] = new ShaderEffectsLibrary.PixelateOutTransition();
            transitionEffects[14] = new ShaderEffectsLibrary.RadialWiggleTransition();
            transitionEffects[15] = new ShaderEffectsLibrary.RandomCircleRevealTransition();
            transitionEffects[16] = new ShaderEffectsLibrary.RippleTransition();
            transitionEffects[17] = new ShaderEffectsLibrary.RotateCrumbleTransition();
            transitionEffects[18] = new ShaderEffectsLibrary.SaturateTransition();
            transitionEffects[19] = new ShaderEffectsLibrary.ShrinkTransition();
            transitionEffects[20] = new ShaderEffectsLibrary.SmoothSwirlGridTransition();
            transitionEffects[21] = new ShaderEffectsLibrary.SwirlGridTransition();
            transitionEffects[22] = new ShaderEffectsLibrary.SwirlTransition();
            transitionEffects[23] = new ShaderEffectsLibrary.WaterTransition();
            transitionEffects[24] = new ShaderEffectsLibrary.WaveTransition();
        }
        private static TransitionEffect GetRandomTransition()
        {
            if(transitionEffects == null)
                return null;
            return transitionEffects[Convert.ToInt32(r.NextDouble() * transitionEffects.Length) % transitionEffects.Length];
        }
        public static void BeginAnimation(UserControl oldControl, UserControl newControl)
        {
            if (IsReady == false)
                Init();

            WriteableBitmap capture = new WriteableBitmap(oldControl, new System.Windows.Media.ScaleTransform());
            System.Windows.Media.ImageBrush imageBrush = new System.Windows.Media.ImageBrush();
            imageBrush.ImageSource = capture;

            TransitionEffect transitionEffect = GetRandomTransition();
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
            da.Duration = TimeSpan.FromSeconds(2);
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
