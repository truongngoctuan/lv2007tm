using Microsoft.Xna.Framework.Graphics;
using Microsoft.Xna.Framework;
using _3DPresentation.Models;
using _3DPresentation.Effects;
using _3DPresentation;
using Babylon.Toolbox;
using System.ComponentModel;

namespace _3DPresentation.Material
{
    public class VertexColorMaterial : BaseMaterial
    {
        [Category("Diffuse")]
        public GlobalVars.ColorEnum DiffuseColor { get; set; }
        [Category("Ambient")]
        public GlobalVars.ColorEnum AmbientColor { get; set; }
        [Category("Ambient")]
        public GlobalVars.ColorEnum SceneAmbientColor { get; set; }
        [Category("Emissive")]
        public GlobalVars.ColorEnum EmissiveColor { get; set; }
        [Category("Specular")]
        public GlobalVars.ColorEnum SpecularColor { get; set; }
        [Category("Specular")]
        public float SpecularPower { get; set; }
        [Category("Position")]
        public Vector3 LightPosition { get; set; }
        public Vector3 CameraPosition { get; set; }
        [Category("Alpha")]
        public float Alpha { get; set; }

        public VertexColorMaterial()
        {
            AmbientColor = GlobalVars.ColorEnum.Green;
            SceneAmbientColor = GlobalVars.ColorEnum.Green;
        }

        public override void Apply()
        {
            VertexColorEffect vertexColorEffect = EffectManager.VertexColorEffect;
            vertexColorEffect.View = EffectManager.Scene.GetCameraView();
            vertexColorEffect.Projection = EffectManager.Scene.GetCameraProjection();
            vertexColorEffect.World = World;

            vertexColorEffect.DiffuseColor = GlobalVars.GetColor(DiffuseColor);

            vertexColorEffect.AmbientColor = GlobalVars.GetColor(AmbientColor);
            vertexColorEffect.SceneAmbientColor = GlobalVars.GetColor(SceneAmbientColor);

            vertexColorEffect.EmissiveColor = GlobalVars.GetColor(EmissiveColor);

            vertexColorEffect.SpecularColor = GlobalVars.GetColor(SpecularColor);
            vertexColorEffect.SpecularPower = SpecularPower;

            vertexColorEffect.LightPosition = LightPosition;
            vertexColorEffect.CameraPosition = EffectManager.Scene.GetCameraPosition();

            vertexColorEffect.Alpha = Alpha;

            vertexColorEffect.Device = Device;
            vertexColorEffect.Apply();
        }

        public override void Save(System.IO.StreamWriter writer, string texturePath)
        {
            if (writer == null)
                return;

            writer.WriteLine("VertexColorEffect");
            writer.WriteLine(ColorToString(DiffuseColor));
            writer.WriteLine(ColorToString(AmbientColor));
            writer.WriteLine(ColorToString(SceneAmbientColor));
            writer.WriteLine(ColorToString(EmissiveColor));
            writer.WriteLine(ColorToString(SpecularColor));
            writer.WriteLine(SpecularPower);
            writer.WriteLine(string.Format("{0} {1} {2}", LightPosition.X, LightPosition.Y, LightPosition.Z));
            writer.WriteLine(Alpha);
        }

        protected override void LoadMaterial(System.IO.StreamReader reader)
        {
            DiffuseColor = ReadColor(reader);
            AmbientColor = ReadColor(reader);
            SceneAmbientColor = ReadColor(reader);
            EmissiveColor = ReadColor(reader);
            SpecularColor = ReadColor(reader);
            SpecularPower = ReadFloat(reader);
            LightPosition = ReadVector3(reader);
            Alpha = ReadFloat(reader);
        }
    }
}
