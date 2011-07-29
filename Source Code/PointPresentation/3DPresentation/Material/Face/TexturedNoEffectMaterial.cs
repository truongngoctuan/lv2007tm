using Microsoft.Xna.Framework.Graphics;
using Microsoft.Xna.Framework;
using _3DPresentation.Models;
using _3DPresentation.Effects;
using System.ComponentModel;

namespace _3DPresentation.Material
{
    public class TexturedNoEffectMaterial : BaseMaterial
    {
        [Category("Texture")]
        [ReadOnly(true)]
        public string DiffuseTexture { get; set; }

        public TexturedNoEffectMaterial()
        {
            DiffuseTexture = "Images/3.jpg";
        }

        public override void Apply()
        {
            Device.BlendState = BlendState.Opaque;
            TexturedNoEffect texturedNoEffect = EffectManager.TexturedNoEffect;
            
            texturedNoEffect.View = EffectManager.Scene.GetCameraView();
            texturedNoEffect.Projection = EffectManager.Scene.GetCameraProjection();
            texturedNoEffect.World = World;
            
            texturedNoEffect.DiffuseTexture = ResourceManager.GetTexture(DiffuseTexture);

            texturedNoEffect.Device = Device;
            texturedNoEffect.Apply();
        }

        public override void Save(System.IO.StreamWriter writer, string texturePath)
        {
            if (writer == null)
                return;

            writer.WriteLine("TexturedMaterial");
            writer.WriteLine(DiffuseTexture);
        }

        protected override void LoadMaterial(System.IO.StreamReader reader)
        {
            DiffuseTexture = reader.ReadLine();
        }
    }
}
