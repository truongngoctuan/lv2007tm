using Microsoft.Xna.Framework;
using Microsoft.Xna.Framework.Graphics;
using Babylon.Toolbox;

namespace _3DPresentation.Effects
{
    public class SimpleEffect : Effect
    {
        readonly EffectParameter worldViewProjectionParameter;
        readonly EffectParameter ambientColorParameter;
        
        public SimpleEffect(GraphicsDevice device)
            : this(device, "3DPresentation", "Effects/SimpleEffect/SimpleEffect")
        {
           
        }

        protected SimpleEffect(GraphicsDevice device, string assemblyName, string rootName)
            : base(device, assemblyName, rootName)
        {
            worldViewProjectionParameter = GetParameter("WorldViewProjection");
            ambientColorParameter = GetParameter("AmbientColor");
        }

        public string Name { get; set; }
        public Matrix World { get; set; }
        public Matrix View { get; set; }
        public Matrix Projection { get; set; }
        public Color AmbientColor { get; set; }

        public override void Apply()
        {
            worldViewProjectionParameter.SetValue(World * View * Projection);
            ambientColorParameter.SetValue(AmbientColor);
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
