using Microsoft.Xna.Framework.Graphics;
using Microsoft.Xna.Framework;
using _3DPresentation.Models;
using _3DPresentation.Effects;

namespace _3DPresentation.Material
{
    public class PointMaterial : BaseMaterial
    {       
        public Vector2 Scale { get; set; }
        public override void Apply()
        {
            PointEffect pointEffect = EffectManager.PointEffect;
            pointEffect.World = World;
            pointEffect.Projection = Projection;
            pointEffect.View = View;
            pointEffect.Scale = Scale;

            pointEffect.Device = Device;
            pointEffect.Apply();
        }
    }
}
