using Microsoft.Xna.Framework.Graphics;
using Microsoft.Xna.Framework;
using _3DPresentation.Models;
using _3DPresentation.Effects;
using System.ComponentModel;

namespace _3DPresentation.Material
{
    public class SimpleEffectMaterial : BaseMaterial
    {
        [Category("Ambient")]
        public GlobalVars.ColorEnum AmbientColor { get; set; }

        public SimpleEffectMaterial()
        {
            AmbientColor = GlobalVars.ColorEnum.White;
        }

        System.DateTime lastTime;
        System.TimeSpan elapsedTime = System.TimeSpan.FromMilliseconds(0);
        public override void Apply()
        {
            if(lastTime == null)
            {
                lastTime = System.DateTime.Now;
            }
            else
            {
                elapsedTime += (System.DateTime.Now - lastTime);
                lastTime = System.DateTime.Now;
                if(elapsedTime.TotalMilliseconds > 1000)
                {
                    AmbientColor = (GlobalVars.ColorEnum)(((int)AmbientColor + 1) % 7);
                    elapsedTime = System.TimeSpan.Zero;
                }
            }
            Device.BlendState = BlendState.Opaque;
            SimpleEffect noEffect = EffectManager.NoEffect;
            noEffect.View = EffectManager.Scene.GetCameraView();
            noEffect.Projection = EffectManager.Scene.GetCameraProjection();
            noEffect.AmbientColor = GlobalVars.GetColor(AmbientColor);
            noEffect.World = World;

            noEffect.Device = Device;
            noEffect.Apply();
        }

        public override void Save(System.IO.StreamWriter writer, string texturePath)
        {
            if (writer == null)
                return;

            writer.WriteLine("NoEffectMaterial");
            writer.WriteLine(ColorToString(AmbientColor));
        }

        protected override void LoadMaterial(System.IO.StreamReader reader)
        {
            AmbientColor = ReadColor(reader);
        }
    }
}
