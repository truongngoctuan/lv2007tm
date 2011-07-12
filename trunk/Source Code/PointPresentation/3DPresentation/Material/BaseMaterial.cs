using System;
using System.Net;
using System.Windows;
using Microsoft.Xna.Framework.Graphics;
using Microsoft.Xna.Framework;
using _3DPresentation.Models;
using _3DPresentation.Effects;
using System.ComponentModel;

namespace _3DPresentation.Material
{
    public abstract class BaseMaterial : INotifyPropertyChanged
    {
        
        public Matrix World { get; set; }
        public GraphicsDevice Device { get; set; }

        public abstract void Apply();


        #region INotifyPropertyChanged Members

        public event PropertyChangedEventHandler PropertyChanged;

        #endregion
    }
}
