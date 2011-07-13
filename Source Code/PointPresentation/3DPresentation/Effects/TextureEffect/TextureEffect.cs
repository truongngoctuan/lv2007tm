using Microsoft.Xna.Framework;
using Microsoft.Xna.Framework.Graphics;
using Babylon.Toolbox;

namespace _3DPresentation.Effects
{
    public class TextureEffect : Effect
    {
        readonly EffectParameter worldParameter;
        readonly EffectParameter worldViewProjectionParameter;

        readonly EffectParameter diffuseSource1Parameter;        
        readonly EffectParameter diffuseColor1Parameter;

        readonly EffectParameter diffuseSource2Parameter;
        readonly EffectParameter diffuseColor2Parameter;

        readonly EffectParameter diffuseSource3Parameter;
        readonly EffectParameter diffuseColor3Parameter;

        readonly EffectParameter diffuseIntensityParameter;
        readonly EffectParameter ambientIntensityParameter;

        readonly SamplerState samplerState;

        public TextureEffect(GraphicsDevice device)
            : this(device, "3DPresentation", "Effects/TextureEffect/TextureEffect")
        {
        }

        protected TextureEffect(GraphicsDevice device, string assemblyName, string rootName)
            : base(device, assemblyName, rootName)
        {
            worldParameter = GetParameter("xWorld");    
            worldViewProjectionParameter = GetParameter("xWorldViewProjection");

            diffuseSource1Parameter = GetParameter("xDiffuseSource1");            
            diffuseColor1Parameter = GetParameter("xDiffuseColor1");

            diffuseSource2Parameter = GetParameter("xDiffuseSource2");
            diffuseColor2Parameter = GetParameter("xDiffuseColor2");

            diffuseSource3Parameter = GetParameter("xDiffuseSource3");
            diffuseColor3Parameter = GetParameter("xDiffuseColor3");

            diffuseIntensityParameter = GetParameter("xDiffuseIntensity");
            ambientIntensityParameter = GetParameter("xAmbientIntensity");

            samplerState = new SamplerState
            {
                AddressU = TextureAddressMode.Wrap,
                AddressV = TextureAddressMode.Wrap,
                AddressW = TextureAddressMode.Wrap,
                Filter = TextureFilter.Linear
            };
        }

        public string Name { get; set; }
        public Matrix World { get; set; }
        public Matrix View { get; set; }
        public Matrix Projection { get; set; }

        public Texture2D DiffuseTexture { get; set; }

        public Vector3 DiffuseSource1 { get; set; }        
        public Color DiffuseColor1 { get; set; }
        public float DiffuseIntensity1 { get; set; }

        public Vector3 DiffuseSource2 { get; set; }
        public Color DiffuseColor2 { get; set; }
        public float DiffuseIntensity2 { get; set; }

        public Vector3 DiffuseSource3 { get; set; }
        public Color DiffuseColor3 { get; set; }
        public float DiffuseIntensity3 { get; set; }

        public float AmbientIntensity { get; set; }

        public override void Apply()
        {
            worldParameter.SetValue(World);
            worldViewProjectionParameter.SetValue(World * View * Projection);

            if (DiffuseTexture != null)
            {
                Device.Textures[0] = DiffuseTexture;
                Device.SamplerStates[0] = samplerState;
            }

            diffuseSource1Parameter.SetValue(DiffuseSource1);
            diffuseColor1Parameter.SetValue(DiffuseColor1);

            diffuseSource2Parameter.SetValue(DiffuseSource2);
            diffuseColor2Parameter.SetValue(DiffuseColor2);

            diffuseSource3Parameter.SetValue(DiffuseSource3);
            diffuseColor3Parameter.SetValue(DiffuseColor3);

            diffuseIntensityParameter.SetValue(new Vector4(DiffuseIntensity1, DiffuseIntensity2, DiffuseIntensity3, 0));
            ambientIntensityParameter.SetValue(new Vector4(AmbientIntensity, 0, 0, 0));
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
