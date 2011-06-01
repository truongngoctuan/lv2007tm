using Microsoft.Xna.Framework;
using Microsoft.Xna.Framework.Graphics;
using Babylon.Toolbox;

namespace _3DPresentation.Effects.NoEffect
{
    public class MyBasicEffect : Effect
    {
        readonly EffectParameter worldParameter;
        readonly EffectParameter worldViewProjectionParameter;

        readonly EffectParameter lightSourceParameter;
        readonly EffectParameter lightIntensityParameter;
        readonly EffectParameter diffuseColorParameter;
        readonly EffectParameter ambientIntensityParameter;

        public MyBasicEffect(GraphicsDevice device)
            : this(device, "3DPresentation", "Effects/MyBasicEffect/MyBasicEffect")
        {
           
        }

        protected MyBasicEffect(GraphicsDevice device, string assemblyName, string rootName)
            : base(device, assemblyName, rootName)
        {
            worldParameter = GetParameter("xWorld");    
            worldViewProjectionParameter = GetParameter("xWorldViewProjection");

            lightSourceParameter = GetParameter("xLightSource");
            lightIntensityParameter = GetParameter("xLightIntensity");
            diffuseColorParameter = GetParameter("xDiffuseColor");
            ambientIntensityParameter = GetParameter("xAmbientIntensity");            
        }

        public string Name { get; set; }
        public Matrix World { get; set; }
        public Matrix View { get; set; }
        public Matrix Projection { get; set; }

        public Vector3 LightSource { get; set; }
        public float LightIntensity { get; set; }
        public Color DiffuseColor { get; set; }
        public float AmbientIntensity { get; set; }

        public override void Apply()
        {
            worldParameter.SetValue(World);
            worldViewProjectionParameter.SetValue(World * View * Projection);
            
            lightSourceParameter.SetValue(LightSource);
            lightIntensityParameter.SetValue(new Vector4(LightIntensity,0,0,0));
            diffuseColorParameter.SetValue(DiffuseColor);
            ambientIntensityParameter.SetValue(new Vector4(AmbientIntensity,0,0,0));
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
