using Microsoft.Xna.Framework.Graphics;
using Microsoft.Xna.Framework;
using _3DPresentation.Models;
using _3DPresentation.Effects;

namespace _3DPresentation.Material
{
    public class TexturedMaterial : BaseMaterial
    {
        public Texture2D DiffuseTexture { get; set; }
        public override void Apply()
        {
            TexturedNoEffect texturedNoEffect = EffectManager.TexturedNoEffect;
            texturedNoEffect.World = World;
            texturedNoEffect.Projection = Projection;
            texturedNoEffect.View = View;
            //texturedNoEffect.DiffuseTexture = DiffuseTexture;

            texturedNoEffect.Device = Device;            
            texturedNoEffect.Apply();
        }
    }
}
