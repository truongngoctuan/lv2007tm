using Microsoft.Xna.Framework;
using Microsoft.Xna.Framework.Graphics;

namespace Babylon
{
    public partial class PerPixelMaterial : Material
    {
        internal PerPixelMaterial(string name, Scene parentScene)
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
            Engine.PerPixelEffect.Alpha = Alpha;
            Engine.PerPixelEffect.AlphaTestEnable = Engine.AlphaTestEnable;

            if (Engine.DiffuseEnable)
                Engine.PerPixelEffect.DiffuseColor = Diffuse * (1.0f - SelfIllumination);
            else
                Engine.PerPixelEffect.DiffuseColor = Color.Black;

            if (Engine.SpecularEnable && SpecularSharpness != 0)
            {
                Engine.PerPixelEffect.SpecularColor = Specular;
                Engine.PerPixelEffect.SpecularPower = SpecularSharpness;
            }
            else
            {
                Engine.PerPixelEffect.SpecularColor = Color.Black;
            }

            if (Engine.EmissiveEnable)
                Engine.PerPixelEffect.EmissiveColor = Emissive * SelfIllumination;
            else
                Engine.PerPixelEffect.EmissiveColor = Color.Black;

            Engine.PerPixelEffect.DiffuseColor = Diffuse;

            Engine.PerPixelEffect.AmbientColor = Utilities.Multiply(Scene.AmbientColor, Ambient);

            // Matrices
            Engine.PerPixelEffect.World = subModel.Parent.World;

            // Textures

            // Diffuse
            if (DiffuseTexture != null && DiffuseTexture.HasTextureData)
            {
                Engine.PerPixelEffect.UseDiffuseTexture = true;
                Engine.Device.Textures[0] = DiffuseTexture.Texture2D;
                Engine.PerPixelEffect.DiffuseTextureMatrix = DiffuseTexture.ComputeTextureMatrix();
                Engine.StatesManager.SetUAddressMode(0, DiffuseTexture.UAddressMode);
                Engine.StatesManager.SetVAddressMode(0, DiffuseTexture.VAddressMode);
                Engine.PerPixelEffect.DiffuseUseCanal2 = DiffuseTexture.MapCoordinatesIndex != 0;
                Engine.PerPixelEffect.DiffuseLevel = DiffuseTexture.Level;
            }
            else
            {
                Engine.PerPixelEffect.UseDiffuseTexture = false;
            }

            // Ambient
            if (AmbientTexture != null && AmbientTexture.HasTextureData)
            {
                Engine.PerPixelEffect.UseAmbientTexture = true;
                Engine.Device.Textures[1] = AmbientTexture.Texture2D;
                Engine.PerPixelEffect.AmbientTextureMatrix = AmbientTexture.ComputeTextureMatrix();
                Engine.StatesManager.SetUAddressMode(1, AmbientTexture.UAddressMode);
                Engine.StatesManager.SetVAddressMode(1, AmbientTexture.VAddressMode);
                Engine.PerPixelEffect.AmbientUseCanal2 = AmbientTexture.MapCoordinatesIndex != 0;
                Engine.PerPixelEffect.AmbientLevel = AmbientTexture.Level;
            }
            else
            {
                Engine.PerPixelEffect.UseAmbientTexture = false;
            }

            // Opacity
            if (OpacityTexture != null && OpacityTexture.HasTextureData)
            {
                Engine.PerPixelEffect.UseOpacityTexture = true;
                Engine.Device.Textures[2] = OpacityTexture.Texture2D;
                Engine.PerPixelEffect.OpacityTextureMatrix = OpacityTexture.ComputeTextureMatrix();
                Engine.StatesManager.SetUAddressMode(2, OpacityTexture.UAddressMode);
                Engine.StatesManager.SetVAddressMode(2, OpacityTexture.VAddressMode);
                Engine.PerPixelEffect.OpacityUseCanal2 = OpacityTexture.MapCoordinatesIndex != 0;
            }
            else
            {
                Engine.PerPixelEffect.UseOpacityTexture = false;
            }

            // Render
            Engine.PerPixelEffect.Apply();

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
