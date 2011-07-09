using Microsoft.Xna.Framework;
using Microsoft.Xna.Framework.Graphics;
using Babylon.Toolbox;

namespace _3DPresentation.Effects
{
    public class TexturedNoEffect : Effect
    {
        readonly EffectParameter worldViewProjectionParameter;

        readonly SamplerState samplerState;

        public TexturedNoEffect(GraphicsDevice device)
            : this(device, "3DPresentation", "Effects/TexturedNoEffect/TexturedNoEffect")
        {
           
        }

        protected TexturedNoEffect(GraphicsDevice device, string assemblyName, string rootName)
            : base(device, assemblyName, rootName)
        {
            worldViewProjectionParameter = GetParameter("WorldViewProjection");

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

        public override void Apply()
        {
            worldViewProjectionParameter.SetValue(World * View * Projection);

            if (DiffuseTexture != null)
            {
                Device.Textures[0] = DiffuseTexture;
                Device.SamplerStates[0] = samplerState;
            }
            base.Apply();
        }

        public override string ToString()
        {
            return Name;
        }

        public override void Dispose()
        {
            base.Dispose();

            DiffuseTexture = null;
        }
    }
}
