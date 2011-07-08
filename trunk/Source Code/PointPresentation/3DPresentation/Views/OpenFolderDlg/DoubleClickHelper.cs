using System;
using System.Windows;
using System.Windows.Input;

namespace FolderDialogSL4
{
    public class DoubleClickHelper
    {
        private long clickedTime = 0;

        public delegate void DoubleClickHandler(object sender, MouseButtonEventArgs e);

        private DoubleClickHandler doubleClickCallBackFunction;
        
        public void AttachDoubleClick(object doubleClickTarget, DoubleClickHandler function)
        {
            UIElement target = (UIElement)doubleClickTarget;
            target.MouseLeftButtonUp += new MouseButtonEventHandler(target_MouseLeftButtonUp);
            target.MouseLeftButtonDown += new MouseButtonEventHandler(target_MouseLeftButtonDown);
            doubleClickCallBackFunction = function;
        }

        private void target_MouseLeftButtonUp(object sender, MouseButtonEventArgs e)
        {
            clickedTime = DateTime.Now.Ticks / 10000;
        }

        private void target_MouseLeftButtonDown(object sender, MouseButtonEventArgs e)
        {
            long currentMillis = DateTime.Now.Ticks / 10000;

            if (currentMillis - clickedTime < 100 && currentMillis - clickedTime > 0)
            {
                doubleClickCallBackFunction(sender, e);
            }

        }
    }
}
