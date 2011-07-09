using System;
using System.Net;
using System.Windows;
using System.Windows.Controls;
using System.Windows.Documents;
using System.Windows.Ink;
using System.Windows.Input;
using System.Windows.Media;
using System.Windows.Media.Animation;
using System.Windows.Shapes;
using System.Windows.Threading;

namespace _3DPresentation
{
    public class Animator
    {
        public EventHandler ValueChanged;
        public EventHandler Completed;
        public double NewValue { get; private set; }

        private static double SPRING = 10;
        private static double EPSILON = 0.5;
        double InitValue { get; set; }
        double FinalValue { get; set; }
        double Spring { get; set; }
        double Epsilon { get; set; }
        int Interval { get; set; }

        DispatcherTimer timer;

        public Animator(double initValue, double finalValue, int interval)
        {
            Spring = SPRING;
            Epsilon = EPSILON;
            InitValue = initValue;
            FinalValue = finalValue;
            Interval = interval;
        }

        public void Run()
        {
            if (timer != null)
            {
                timer.Stop();
                timer = null;
            }
            timer = new DispatcherTimer();
            timer.Interval = TimeSpan.FromMilliseconds(Interval);
            timer.Tick += new EventHandler(timer_Tick);

            NewValue = InitValue;
            timer.Start();
        }

        void timer_Tick(object sender, EventArgs e)
        {
            if (Math.Abs(FinalValue - NewValue) > Epsilon)
            {
                NewValue += (FinalValue - NewValue) / Spring;
                if (ValueChanged != null)
                    ValueChanged(this, EventArgs.Empty);
            }
            else
            {
                NewValue = FinalValue;
                if (Completed != null)
                    Completed(this, EventArgs.Empty);

                timer.Stop();
            }
        }
    }
}
