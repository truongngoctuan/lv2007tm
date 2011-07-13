using Microsoft.Xna.Framework.Graphics;
using Microsoft.Xna.Framework;
using _3DPresentation.Models;
using _3DPresentation.Effects;

namespace _3DPresentation.Material
{
    public class PointMaterial : BaseMaterial
    {
        public override void Apply()
        {
            PointEffect pointEffect = EffectManager.PointEffect;
            pointEffect.View = EffectManager.Scene.GetCameraView();
            pointEffect.Projection = EffectManager.Scene.GetCameraProjection();
            pointEffect.World = World;

            Vector2 drawingSurfaceSize = EffectManager.Scene.GetDrawingSurfaceSize();
            pointEffect.Scale = new Vector2(1.0f / drawingSurfaceSize.X, 1.0f / drawingSurfaceSize.Y);

            pointEffect.Device = Device;
            pointEffect.Apply();
        }

        public override void Save(System.IO.StreamWriter writer, string texturePath)
        {
            if (writer == null)
                return;

            writer.WriteLine("PointMaterial");
        }

        protected override void LoadMaterial(System.IO.StreamReader reader)
        {
            
        }
    }
}
