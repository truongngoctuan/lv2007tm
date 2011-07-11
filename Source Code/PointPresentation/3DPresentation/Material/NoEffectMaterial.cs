using Microsoft.Xna.Framework.Graphics;
using Microsoft.Xna.Framework;
using _3DPresentation.Models;
using _3DPresentation.Effects;

namespace _3DPresentation.Material
{
    public class NoEffectMaterial : BaseMaterial
    {
        public override void Apply()
        {
            NoEffect noEffect = EffectManager.NoEffect;
            noEffect.World = World;
            noEffect.View = View;
            noEffect.Projection = Projection;

            noEffect.Device = Device;
            noEffect.Apply();
        }
    }
}
