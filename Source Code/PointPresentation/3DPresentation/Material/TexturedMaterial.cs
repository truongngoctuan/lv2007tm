using Microsoft.Xna.Framework.Graphics;
using Microsoft.Xna.Framework;
using _3DPresentation.Models;
using _3DPresentation.Effects;

namespace _3DPresentation.Material
{
    public class TexturedMaterial : BaseMaterial
    {
        public string DiffuseTexture { get; set; }
        public override void Apply()
        {
            TexturedNoEffect texturedNoEffect = EffectManager.TexturedNoEffect;
            
            texturedNoEffect.View = EffectManager.Scene.GetCameraView();
            texturedNoEffect.Projection = EffectManager.Scene.GetCameraProjection();
            texturedNoEffect.World = World;
            
            //texturedNoEffect.DiffuseTexture = ResourceManager.GetTexture(DiffuseTexture);

            texturedNoEffect.Device = Device;
            texturedNoEffect.Apply();
        }

        public override void Save(System.IO.StreamWriter writer, string texturePath)
        {
            if (writer == null)
                return;

            writer.WriteLine("TexturedMaterial");
            writer.WriteLine(DiffuseTexture); SaveTexture(texturePath, DiffuseTexture);
        }

        protected override void LoadMaterial(System.IO.StreamReader reader)
        {
            DiffuseTexture = reader.ReadLine();
        }
    }
}
