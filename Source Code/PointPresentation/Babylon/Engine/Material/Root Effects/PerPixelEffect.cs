using Babylon.Toolbox;
using Microsoft.Xna.Framework;

namespace Babylon
{
    public class PerPixelEffect
    {
        readonly Effect effect;
        readonly EffectParameter worldViewProjectionParameter;
        readonly EffectParameter worldParameter;
        readonly EffectParameter lightInfoParameter;
        readonly EffectParameter diffuseColorParameter;
        readonly EffectParameter specularColorParameter;
        readonly EffectParameter emissiveColorParameter;
        readonly EffectParameter ambientColorParameter;
        readonly EffectParameter eyePositionParameter;
        readonly EffectParameter diffuseTextureMatrixParameter;
        readonly EffectParameter ambientTextureMatrixParameter;
        readonly EffectParameter opacityTextureMatrixParameter;
        readonly EffectParameter booleans01Parameter;
        readonly EffectParameter booleans02Parameter;
        readonly EffectParameter levelsParameter;

        // Matrices
        public Matrix World { get; set; }
        public Matrix View { get; set; }
        public Matrix Projection { get; set; }

        // Textures
        public bool DiffuseUseCanal2 { get; set; }
        public bool AmbientUseCanal2 { get; set; }
        public bool OpacityUseCanal2 { get; set; }
        public Matrix DiffuseTextureMatrix { get; set; }
        public Matrix AmbientTextureMatrix { get; set; }
        public Matrix OpacityTextureMatrix { get; set; }
        
        // Light
        public Vector3 LightInfo { get; set; }
        public bool LighIsPoint { get; set; }
        public Color LightDiffuseColor { get; set; }
        public Color LightSpecularColor { get; set; }

        // Camera
        public Vector3 EyePosition { get; set; }

        // Colors
        public float Alpha { get; set; }
        public Color AmbientColor { get; set; }
        public Color DiffuseColor { get; set; }
        public Color SpecularColor { get; set; }
        public Color EmissiveColor { get; set; }
        public float SpecularPower { get; set; }

        // Bools
        public bool UseDiffuseTexture { get; set; }
        public bool UseAmbientTexture { get; set; }
        public bool UseOpacityTexture { get; set; }
        public bool AlphaTestEnable { get; set; }

        // Levels
        public float DiffuseLevel { get; set; }
        public float AmbientLevel { get; set; }


        public PerPixelEffect(Engine engine)
        {
            effect = new Effect(engine.Device, "Babylon", "Engine/Shaders/perpixel");
            worldViewProjectionParameter = effect.GetParameter("WorldViewProjection");
            worldParameter = effect.GetParameter("World");
            lightInfoParameter = effect.GetParameter("LightInfo");
            diffuseColorParameter = effect.GetParameter("DiffuseColor");
            specularColorParameter = effect.GetParameter("SpecularColor");
            emissiveColorParameter = effect.GetParameter("EmissiveColor");
            ambientColorParameter = effect.GetParameter("AmbientColor");
            eyePositionParameter = effect.GetParameter("EyePosition");
            diffuseTextureMatrixParameter = effect.GetParameter("DiffuseTextureMatrix");
            ambientTextureMatrixParameter = effect.GetParameter("AmbientTextureMatrix");
            opacityTextureMatrixParameter = effect.GetParameter("OpacityTextureMatrix");

            booleans01Parameter = effect.GetParameter("Booleans01");
            booleans02Parameter = effect.GetParameter("Booleans02");
            levelsParameter = effect.GetParameter("Levels");
        }

        public void Apply()
        {
            worldViewProjectionParameter.SetValue(World * View * Projection);
            worldParameter.SetValue(World);

            lightInfoParameter.SetValue(new Vector4(LightInfo, LighIsPoint ? 1 : 0));

            diffuseColorParameter.SetValue(Utilities.Multiply(DiffuseColor, LightDiffuseColor), Alpha);
            specularColorParameter.SetValue(Utilities.Multiply(SpecularColor, LightSpecularColor), SpecularPower);
            emissiveColorParameter.SetValue(EmissiveColor);
            ambientColorParameter.SetValue(AmbientColor);

            eyePositionParameter.SetValue(EyePosition);

            diffuseTextureMatrixParameter.SetValue(DiffuseTextureMatrix);
            ambientTextureMatrixParameter.SetValue(AmbientTextureMatrix);
            opacityTextureMatrixParameter.SetValue(OpacityTextureMatrix);

            booleans01Parameter.SetValue(UseDiffuseTexture, UseAmbientTexture, DiffuseUseCanal2, AmbientUseCanal2);

            booleans02Parameter.SetValue(UseOpacityTexture, OpacityUseCanal2, AlphaTestEnable, false);

            levelsParameter.SetValue(DiffuseLevel, AmbientLevel, 0, 0);

            effect.Apply();
        }

        internal void Prepare(Scene scene)
        {
            // View & Projection
            View = scene.ActiveCamera.View;
            Projection = scene.ActiveCamera.Projection;
            EyePosition = scene.ActiveCamera.Position;

            // Lights
            if (scene.Lights.Count > 0)
            {
                LightInfo = scene.Lights[0].Type == LightType.Directional ? scene.Lights[0].Direction : scene.Lights[0].Position;
                LighIsPoint = scene.Lights[0].Type != LightType.Directional;
                LightDiffuseColor = scene.Lights[0].Diffuse;
                LightSpecularColor = scene.Lights[0].Specular;
            }
            else
            {
                LightInfo = Vector3.Zero;
                LighIsPoint = false;
            }
        }
    }
}
