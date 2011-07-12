using Microsoft.Xna.Framework.Graphics;
using Microsoft.Xna.Framework;
using _3DPresentation.Models;
using _3DPresentation.Effects;
using _3DPresentation;
using System.ComponentModel;

namespace _3DPresentation.Material
{
    public class FourPointLightsMaterial : BaseMaterial
    {
        public Vector3 LightSource1 { get; set; }
        public GlobalVars.ColorEnum LightColor1 { get; set; }
        public bool EnableLight1 { get; set; }

        public Vector3 LightSource2 { get; set; }
        public GlobalVars.ColorEnum LightColor2 { get; set; }
        public bool EnableLight2 { get; set; }

        public Vector3 LightSource3 { get; set; }
        public GlobalVars.ColorEnum LightColor3 { get; set; }
        public bool EnableLight3 { get; set; }

        public Vector3 LightSource4 { get; set; }
        public GlobalVars.ColorEnum LightColor4 { get; set; }
        public bool EnableLight4 { get; set; }

        public GlobalVars.ColorEnum AmbientLight { get; set; }

        public override void Apply()
        {
            FourPointLightsEffect fourPointLights = EffectManager.FourPointLightsEffect;
            fourPointLights.View = EffectManager.Scene.GetCameraView();
            fourPointLights.Projection = EffectManager.Scene.GetCameraProjection();
            fourPointLights.World = World;

            fourPointLights.LightColor1 = GlobalVars.GetColor(LightColor1);
            fourPointLights.LightSource1 = LightSource1;
            fourPointLights.EnableLight1 = EnableLight1;

            fourPointLights.LightColor2 = GlobalVars.GetColor(LightColor2);
            fourPointLights.LightSource2 = LightSource2;
            fourPointLights.EnableLight2 = EnableLight2;

            fourPointLights.LightColor3 = GlobalVars.GetColor(LightColor3);
            fourPointLights.LightSource3 = LightSource3;
            fourPointLights.EnableLight3 = EnableLight3;

            fourPointLights.LightColor4 = GlobalVars.GetColor(LightColor4);
            fourPointLights.LightSource4 = LightSource4;
            fourPointLights.EnableLight4 = EnableLight4;

            fourPointLights.Device = Device;
            fourPointLights.Apply();
        }
    }
}
