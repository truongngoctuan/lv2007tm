using Microsoft.Xna.Framework.Graphics;
using Microsoft.Xna.Framework;
using _3DPresentation.Models;
using _3DPresentation.Effects;
using System.ComponentModel;
using Babylon.Toolbox;

namespace _3DPresentation.Material
{
    public class BasicMaterial : BaseMaterial
    {
        [Category("Diffuse")]
        public GlobalVars.ColorEnum DiffuseColor { get; set; }
        [Category("Diffuse")]
        [ReadOnly(true)]
        public string DiffuseTexture { get; set; }
        [Category("Ambient")]
        public GlobalVars.ColorEnum AmbientColor { get; set; }
        [Category("Ambient")]
        public GlobalVars.ColorEnum SceneAmbientColor { get; set; }
        [Category("Emissive")]
        public GlobalVars.ColorEnum EmissiveColor { get; set; }
        [Category("Specular")]
        [ReadOnly(true)]
        public string SpecularTexture { get; set; }
        [Category("Specular")]
        public GlobalVars.ColorEnum SpecularColor { get; set; }
        [Category("Specular")]
        public float SpecularPower { get; set; }
        [Category("Bump")]
        [ReadOnly(true)]
        public string BumpTexture { get; set; }
        [Category("Position")]
        public Vector3 LightPosition { get; set; }
        [Category("Misc")]
        public bool InvertBinormal { get; set; }
        [Category("Misc")]
        public float Alpha { get; set; }

        public override void Apply()
        {
            BasicEffect basicEffect = EffectManager.BasicEffect;
            basicEffect.View = EffectManager.Scene.GetCameraView();
            basicEffect.Projection = EffectManager.Scene.GetCameraProjection();
            basicEffect.World = World;

            basicEffect.DiffuseColor = GlobalVars.GetColor(DiffuseColor);
            basicEffect.DiffuseTexture = ResourceManager.GetTexture(DiffuseTexture);

            basicEffect.AmbientColor = GlobalVars.GetColor(AmbientColor);
            basicEffect.SceneAmbientColor = GlobalVars.GetColor(SceneAmbientColor);

            basicEffect.EmissiveColor = GlobalVars.GetColor(EmissiveColor);

            basicEffect.SpecularTexture = ResourceManager.GetTexture(SpecularTexture);
            basicEffect.SpecularColor = GlobalVars.GetColor(SpecularColor);
            basicEffect.SpecularPower = SpecularPower;

            basicEffect.BumpTexture = ResourceManager.GetTexture(BumpTexture);

            basicEffect.LightPosition = LightPosition;
            basicEffect.CameraPosition = EffectManager.Scene.GetCameraPosition();

            basicEffect.InvertBinormal = InvertBinormal;

            basicEffect.Alpha = Alpha;

            basicEffect.Device = Device;
            basicEffect.Apply();
        }

        public override void Save(System.IO.StreamWriter writer, string texturePath)
        {
            if (writer == null)
                return;
            
            writer.WriteLine("BasicMaterial");
            writer.WriteLine(ColorToString(DiffuseColor));
            if (DiffuseTexture == null)
                writer.WriteLine("null");
            else
                writer.WriteLine(DiffuseTexture); SaveTexture(texturePath, DiffuseTexture);

            writer.WriteLine(ColorToString(AmbientColor));
            writer.WriteLine(ColorToString(SceneAmbientColor));

            writer.WriteLine(ColorToString(EmissiveColor));

            if (SpecularTexture == null)
                writer.WriteLine("null");
            else
                writer.WriteLine(SpecularTexture); SaveTexture(texturePath, SpecularTexture);
            writer.WriteLine(ColorToString(SpecularColor));
            writer.WriteLine(SpecularPower);

            if (BumpTexture == null)
                writer.WriteLine("null");
            else
                writer.WriteLine(BumpTexture); SaveTexture(texturePath, BumpTexture);

            writer.WriteLine(string.Format("{0} {1} {2}", LightPosition.X, LightPosition.Y, LightPosition.Z));
            writer.WriteLine(InvertBinormal);
            writer.WriteLine(Alpha);
        }        

        protected override void LoadMaterial(System.IO.StreamReader reader)
        {
            DiffuseColor = ReadColor(reader);
            DiffuseTexture = reader.ReadLine();

            AmbientColor = ReadColor(reader);
            SceneAmbientColor = ReadColor(reader);

            EmissiveColor = ReadColor(reader);

            SpecularTexture = reader.ReadLine();
            SpecularColor = ReadColor(reader);
            SpecularPower = ReadFloat(reader);

            BumpTexture = reader.ReadLine();

            LightPosition = ReadVector3(reader);

            InvertBinormal = ReadBool(reader);

            Alpha = ReadFloat(reader);
        }
    }
}
