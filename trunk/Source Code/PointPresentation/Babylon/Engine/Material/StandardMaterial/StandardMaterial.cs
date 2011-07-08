using Microsoft.Xna.Framework;
using Microsoft.Xna.Framework.Graphics;

namespace Babylon
{
    public partial class StandardMaterial : Material
    {
        internal StandardMaterial(string name, Scene parentScene)
            : base(name, parentScene)
        {
            SpecularSharpness = 1.0f;
            Emissive = Color.Black;
            Specular = Color.White;
            Diffuse = Color.White;
            Ambient = Color.Black;
        }

        public Texture DiffuseTexture { get; set; }

        public Texture AmbientTexture { get; set; }

        public Texture OpacityTexture { get; set; }

        public Color Ambient { get; set; }

        public Color Diffuse { get; set; }

        public Color Specular { get; set; }

        public Color Emissive { get; set; }

        public float SelfIllumination { get; set; }

        public float SpecularSharpness { get; set; }

        public override bool IsOpacity
        {
            get { return DiffuseTexture != null && DiffuseTexture.HasTextureData && DiffuseTexture.HasAlpha; }
        }

        public override void Render(SubModel subModel)
        {
            // States
            Engine.StatesManager.CullMode = CullMode;
            Engine.StatesManager.FillMode = Scene.ForceWireframe ? FillMode.WireFrame : FillMode;

            // Colors
            Engine.StandardEffect.Alpha = Alpha;
            Engine.StandardEffect.AlphaTestEnable = Engine.AlphaTestEnable;

            if (Engine.DiffuseEnable)
                Engine.StandardEffect.DiffuseColor = Diffuse * (1.0f - SelfIllumination);
            else
                Engine.StandardEffect.DiffuseColor = Color.Black;

            if (Engine.SpecularEnable && SpecularSharpness != 0)
            {
                Engine.StandardEffect.SpecularColor = Specular;
                Engine.StandardEffect.SpecularPower = SpecularSharpness;
            }
            else
            {
                Engine.StandardEffect.SpecularColor = Color.Black;
            }

            if (Engine.EmissiveEnable)
                Engine.StandardEffect.EmissiveColor = Emissive * SelfIllumination;
            else
                Engine.StandardEffect.EmissiveColor = Color.Black;

            Engine.StandardEffect.DiffuseColor = Diffuse;

            Engine.StandardEffect.AmbientColor = Utilities.Multiply(Scene.AmbientColor, Ambient);

            // Matrices
            Engine.StandardEffect.World = subModel.Parent.World;

            // Textures

            // Diffuse
            if (DiffuseTexture != null && DiffuseTexture.HasTextureData)
            {
                Engine.StandardEffect.UseDiffuseTexture = true;
                Engine.Device.Textures[0] = DiffuseTexture.Texture2D;
                Engine.StandardEffect.DiffuseTextureMatrix = DiffuseTexture.ComputeTextureMatrix();
                Engine.StatesManager.SetUAddressMode(0, DiffuseTexture.UAddressMode);
                Engine.StatesManager.SetVAddressMode(0, DiffuseTexture.VAddressMode);
                Engine.StandardEffect.DiffuseUseCanal2 = DiffuseTexture.MapCoordinatesIndex != 0;
                Engine.StandardEffect.DiffuseLevel = DiffuseTexture.Level;
            }
            else
            {
                Engine.StandardEffect.UseDiffuseTexture = false;
            }

            // Ambient
            if (AmbientTexture != null && AmbientTexture.HasTextureData)
            {
                Engine.StandardEffect.UseAmbientTexture = true;
                Engine.Device.Textures[1] = AmbientTexture.Texture2D;
                Engine.StandardEffect.AmbientTextureMatrix = AmbientTexture.ComputeTextureMatrix();
                Engine.StatesManager.SetUAddressMode(1, AmbientTexture.UAddressMode);
                Engine.StatesManager.SetVAddressMode(1, AmbientTexture.VAddressMode);
                Engine.StandardEffect.AmbientUseCanal2 = AmbientTexture.MapCoordinatesIndex != 0;
                Engine.StandardEffect.AmbientLevel = AmbientTexture.Level;
            }
            else
            {
                Engine.StandardEffect.UseAmbientTexture = false;
            }

            // Opacity
            if (OpacityTexture != null && OpacityTexture.HasTextureData)
            {
                Engine.StandardEffect.UseOpacityTexture = true;
                Engine.Device.Textures[2] = OpacityTexture.Texture2D;
                Engine.StandardEffect.OpacityTextureMatrix = OpacityTexture.ComputeTextureMatrix();
                Engine.StatesManager.SetUAddressMode(2, OpacityTexture.UAddressMode);
                Engine.StatesManager.SetVAddressMode(2, OpacityTexture.VAddressMode);
                Engine.StandardEffect.OpacityUseCanal2 = OpacityTexture.MapCoordinatesIndex != 0;
            }
            else
            {
                Engine.StandardEffect.UseOpacityTexture = false;
            }

            // Render
            Engine.StandardEffect.Apply();

            Engine.Device.SetVertexBuffer(subModel.Parent.VertexBuffer);
            Engine.Device.Indices = subModel.Parent.IndexBuffer;

            Engine.Device.DrawIndexedPrimitives(PrimitiveType.TriangleList, 0, subModel.MinVertexIndex, subModel.VerticesCount, subModel.StartIndex, subModel.FacesCount);
        }

        public override void Dispose()
        {
            if (DiffuseTexture != null)
            {
                DiffuseTexture.Dispose();
                DiffuseTexture = null;
            }

            if (AmbientTexture != null)
            {
                AmbientTexture.Dispose();
                AmbientTexture = null;
            }

            if (OpacityTexture != null)
            {
                OpacityTexture.Dispose();
                OpacityTexture = null;
            }

            base.Dispose();
        }
    }
}
