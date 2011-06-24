using Microsoft.Xna.Framework;
using Microsoft.Xna.Framework.Graphics;
using Babylon.Toolbox;

namespace _3DPresentation.Effects.PointEffect
{
    public class PointEffect : Effect
    {
        readonly EffectParameter worldViewProjectionParameter;
        readonly EffectParameter scaleParameter;

        public PointEffect(GraphicsDevice device)
            : this(device, "3DPresentation", "Effects/PointEffect/PointEffect")
        {
           
        }

        protected PointEffect(GraphicsDevice device, string assemblyName, string rootName)
            : base(device, assemblyName, rootName)
        {
            worldViewProjectionParameter = GetParameter("WorldViewProjection");
            scaleParameter = GetParameter("Scale");
        }

        public string Name { get; set; }
        public Matrix World { get; set; }
        public Matrix View { get; set; }
        public Matrix Projection { get; set; }
        public Vector2 Scale { get; set; }

        public override void Apply()
        {
            worldViewProjectionParameter.SetValue(World * View * Projection);
            scaleParameter.SetValue(new Vector4(Scale.X, Scale.Y, 0.0f, 0.0f));
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
