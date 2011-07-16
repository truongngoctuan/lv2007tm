using Microsoft.Xna.Framework.Graphics;
using Microsoft.Xna.Framework;
using _3DPresentation.Models;
using _3DPresentation.Effects;
using _3DPresentation;
using System.ComponentModel;

namespace _3DPresentation.Material
{
    public class TextureMaterial : BaseMaterial
    {
        [Category("Texture")]
        [ReadOnly(true)]
        public string DiffuseTexture { get; set; }

        [Category("Ambient Light")]
        public float AmbientIntensity { get; set; }

        [Category("Point Light 1")]
        public Vector3 DiffuseSource1 { get; set; }
        [Category("Point Light 1")]
        public GlobalVars.ColorEnum DiffuseColor1 { get; set; }
        [Category("Point Light 1")]
        public float DiffuseIntensity1 { get; set; }

        [Category("Point Light 2")]
        public Vector3 DiffuseSource2 { get; set; }
        [Category("Point Light 2")]
        public GlobalVars.ColorEnum DiffuseColor2 { get; set; }
        [Category("Point Light 2")]
        public float DiffuseIntensity2 { get; set; }

        [Category("Point Light 3")]
        public Vector3 DiffuseSource3 { get; set; }
        [Category("Point Light 3")]
        public GlobalVars.ColorEnum DiffuseColor3 { get; set; }
        [Category("Point Light 3")]
        public float DiffuseIntensity3 { get; set; }

        public TextureMaterial()
        {
            AmbientIntensity = 0.3f;
        }

        public override void Apply()
        {
            Device.BlendState = BlendState.Opaque;
            TextureEffect textureEffect = EffectManager.TextureEffect;
            textureEffect.View = EffectManager.Scene.GetCameraView();
            textureEffect.Projection = EffectManager.Scene.GetCameraProjection();
            textureEffect.World = World;

            textureEffect.DiffuseTexture = ResourceManager.GetTexture(DiffuseTexture);

            textureEffect.AmbientIntensity = AmbientIntensity;

            textureEffect.DiffuseSource1 = DiffuseSource1;
            textureEffect.DiffuseColor1 = GlobalVars.GetColor(DiffuseColor1);
            textureEffect.DiffuseIntensity1 = DiffuseIntensity1;

            textureEffect.DiffuseSource2 = DiffuseSource2;
            textureEffect.DiffuseColor2 = GlobalVars.GetColor(DiffuseColor2);
            textureEffect.DiffuseIntensity2 = DiffuseIntensity2;

            textureEffect.DiffuseSource3 = DiffuseSource3;
            textureEffect.DiffuseColor3 = GlobalVars.GetColor(DiffuseColor3);
            textureEffect.DiffuseIntensity3 = DiffuseIntensity3;

            textureEffect.Device = Device;
            textureEffect.Apply();

            if (EffectManager.Scene is ViewScene)
            {
                if (DiffuseIntensity1 > 0)
                    ((ViewScene)EffectManager.Scene).SetLightPosition(0, DiffuseSource1, DiffuseColor1);
                if (DiffuseIntensity2 > 0)
                    ((ViewScene)EffectManager.Scene).SetLightPosition(1, DiffuseSource2, DiffuseColor2);
                if (DiffuseIntensity3 > 0)
                    ((ViewScene)EffectManager.Scene).SetLightPosition(2, DiffuseSource3, DiffuseColor3);
            }
        }

        public override void Save(System.IO.StreamWriter writer, string texturePath)
        {
            if (writer == null)
                return;

            writer.WriteLine("TextureMaterial");
            if (DiffuseTexture == null)
                writer.WriteLine(" ");
            else
            {
                writer.WriteLine(DiffuseTexture); 
                SaveTexture(texturePath, DiffuseTexture);
            }
            

            writer.WriteLine(AmbientIntensity);

            writer.WriteLine(string.Format("{0} {1} {2}", DiffuseSource1.X, DiffuseSource1.Y, DiffuseSource1.Z));
            writer.WriteLine(ColorToString(DiffuseColor1));
            writer.WriteLine(DiffuseIntensity1);

            writer.WriteLine(string.Format("{0} {1} {2}", DiffuseSource2.X, DiffuseSource2.Y, DiffuseSource2.Z));
            writer.WriteLine(ColorToString(DiffuseColor2));
            writer.WriteLine(DiffuseIntensity2);

            writer.WriteLine(string.Format("{0} {1} {2}", DiffuseSource3.X, DiffuseSource3.Y, DiffuseSource3.Z));
            writer.WriteLine(ColorToString(DiffuseColor3));
            writer.WriteLine(DiffuseIntensity3);
        }

        protected override void LoadMaterial(System.IO.StreamReader reader)
        {
            DiffuseTexture = reader.ReadLine();

            AmbientIntensity = ReadFloat(reader);

            DiffuseSource1 = ReadVector3(reader);
            DiffuseColor1 = ReadColor(reader);
            DiffuseIntensity1 = ReadFloat(reader);

            DiffuseSource2 = ReadVector3(reader);
            DiffuseColor2 = ReadColor(reader);
            DiffuseIntensity2 = ReadFloat(reader);

            DiffuseSource3 = ReadVector3(reader);
            DiffuseColor3 = ReadColor(reader);
            DiffuseIntensity3 = ReadFloat(reader);
        }
    }
}
