using System;
using System.Net;
using System.Windows;
using Microsoft.Xna.Framework.Graphics;
using Microsoft.Xna.Framework;
using _3DPresentation.Models;
using _3DPresentation.Effects;

namespace _3DPresentation.Material
{
    public abstract class BaseMaterial
    {
        public Matrix World { get; set; }
        public Matrix View { get; set; }
        public Matrix Projection { get; set; }
        public GraphicsDevice Device { get; set; }

        public abstract void Apply();
    }
}
