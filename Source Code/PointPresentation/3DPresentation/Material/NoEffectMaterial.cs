using Microsoft.Xna.Framework.Graphics;
using Microsoft.Xna.Framework;
using _3DPresentation.Models;
using _3DPresentation.Effects;
using System.ComponentModel;

namespace _3DPresentation.Material
{
    public class NoEffectMaterial : BaseMaterial
    {
        [Category("Info")]
        public double TestValue { get; set; }

        public override void Apply()
        {
            NoEffect noEffect = EffectManager.NoEffect;
            noEffect.View = EffectManager.Scene.GetCameraView();
            noEffect.Projection = EffectManager.Scene.GetCameraProjection();
            noEffect.World = World;

            noEffect.Device = Device;
            noEffect.Apply();
        }

        public override void Save(System.IO.StreamWriter writer, string texturePath)
        {
            if (writer == null)
                return;

            writer.WriteLine("NoEffectMaterial");
        }

        protected override void LoadMaterial(System.IO.StreamReader reader)
        {
            
        }
    }
}
