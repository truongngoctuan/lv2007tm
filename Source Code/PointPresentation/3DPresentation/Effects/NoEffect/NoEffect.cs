using Microsoft.Xna.Framework;
using Microsoft.Xna.Framework.Graphics;
using Babylon.Toolbox;

namespace _3DPresentation.Effects
{
    public class NoEffect : Effect
    {
        readonly EffectParameter worldViewProjectionParameter;

        public NoEffect(GraphicsDevice device)
            : this(device, "3DPresentation", "Effects/NoEffect/NoEffect")
        {
           
        }

        protected NoEffect(GraphicsDevice device, string assemblyName, string rootName)
            : base(device, assemblyName, rootName)
        {
            worldViewProjectionParameter = GetParameter("WorldViewProjection");
        }

        public string Name { get; set; }
        public Matrix World { get; set; }
        public Matrix View { get; set; }
        public Matrix Projection { get; set; }

        public override void Apply()
        {
            worldViewProjectionParameter.SetValue(World * View * Projection);
            base.Apply();
        }

        public override string ToString()
        {
            return Name;
        }

        public override void Dispose()
        {
            base.Dispose();
        }
    }
}
