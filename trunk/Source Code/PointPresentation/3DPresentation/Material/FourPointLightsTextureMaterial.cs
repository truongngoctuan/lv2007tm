﻿using Microsoft.Xna.Framework.Graphics;
using Microsoft.Xna.Framework;
using _3DPresentation.Models;
using _3DPresentation.Effects;
using _3DPresentation;
using System.ComponentModel;

namespace _3DPresentation.Material
{
    public class FourPointLightsTextureMaterial : BaseMaterial
    {
        [Category("Texture")]
        [ReadOnly(true)]
        public string DiffuseTexture { get; set; }

        [Category("AmbientLight")]
        public GlobalVars.ColorEnum AmbientLight { get; set; }

        [Category("Point Light 1")]
        public Vector3 LightSource1 { get; set; }
        [Category("Point Light 1")]
        public GlobalVars.ColorEnum LightColor1 { get; set; }
        [Category("Point Light 1")]
        public bool EnableLight1 { get; set; }

        [Category("Point Light 2")]
        public Vector3 LightSource2 { get; set; }
        [Category("Point Light 2")]
        public GlobalVars.ColorEnum LightColor2 { get; set; }
        [Category("Point Light 2")]
        public bool EnableLight2 { get; set; }

        [Category("Point Light 3")]
        public Vector3 LightSource3 { get; set; }
        [Category("Point Light 3")]
        public GlobalVars.ColorEnum LightColor3 { get; set; }
        [Category("Point Light 3")]
        public bool EnableLight3 { get; set; }

        [Category("Point Light 4")]
        public Vector3 LightSource4 { get; set; }
        [Category("Point Light 4")]
        public GlobalVars.ColorEnum LightColor4 { get; set; }
        [Category("Point Light 4")]
        public bool EnableLight4 { get; set; }

        public override void Apply()
        {
            FourPointLightsTextureEffect fourPointLights = EffectManager.FourPointLightsTextureEffect;
            fourPointLights.View = EffectManager.Scene.GetCameraView();
            fourPointLights.Projection = EffectManager.Scene.GetCameraProjection();
            fourPointLights.World = World;

            fourPointLights.DiffuseTexture = ResourceManager.GetTexture(DiffuseTexture);
            fourPointLights.AmbientLight = GlobalVars.GetColor(AmbientLight);

            fourPointLights.LightSource1 = LightSource1;
            fourPointLights.LightColor1 = GlobalVars.GetColor(LightColor1);            
            fourPointLights.EnableLight1 = EnableLight1;

            fourPointLights.LightSource2 = LightSource2;
            fourPointLights.LightColor2 = GlobalVars.GetColor(LightColor2);            
            fourPointLights.EnableLight2 = EnableLight2;

            fourPointLights.LightSource3 = LightSource3;
            fourPointLights.LightColor3 = GlobalVars.GetColor(LightColor3);            
            fourPointLights.EnableLight3 = EnableLight3;

            fourPointLights.LightSource4 = LightSource4;
            fourPointLights.LightColor4 = GlobalVars.GetColor(LightColor4);            
            fourPointLights.EnableLight4 = EnableLight4;

            fourPointLights.Device = Device;
            fourPointLights.Apply();
        }

        public override void Save(System.IO.StreamWriter writer, string texturePath)
        {
            if (writer == null)
                return;

            writer.WriteLine("FourPointLightsEffect");
            writer.WriteLine(DiffuseTexture);

            writer.WriteLine(ColorToString(AmbientLight));

            writer.WriteLine(string.Format("{0} {1} {2}", LightSource1.X, LightSource1.Y, LightSource1.Z));
            writer.WriteLine(ColorToString(LightColor1));
            writer.WriteLine(EnableLight1);

            writer.WriteLine(string.Format("{0} {1} {2}", LightSource2.X, LightSource2.Y, LightSource2.Z));
            writer.WriteLine(ColorToString(LightColor2));
            writer.WriteLine(EnableLight2);

            writer.WriteLine(string.Format("{0} {1} {2}", LightSource3.X, LightSource3.Y, LightSource3.Z));
            writer.WriteLine(ColorToString(LightColor3));
            writer.WriteLine(EnableLight3);

            writer.WriteLine(string.Format("{0} {1} {2}", LightSource4.X, LightSource4.Y, LightSource4.Z));
            writer.WriteLine(ColorToString(LightColor4));
            writer.WriteLine(EnableLight4);
        }

        protected override void LoadMaterial(System.IO.StreamReader reader)
        {
            DiffuseTexture = reader.ReadLine();

            AmbientLight = ReadColor(reader);

            LightSource1 = ReadVector3(reader);
            LightColor1 = ReadColor(reader);
            EnableLight1 = ReadBool(reader);

            LightSource2 = ReadVector3(reader);
            LightColor2 = ReadColor(reader);
            EnableLight2 = ReadBool(reader);

            LightSource3 = ReadVector3(reader);
            LightColor3 = ReadColor(reader);
            EnableLight3 = ReadBool(reader);

            LightSource4 = ReadVector3(reader);
            LightColor4 = ReadColor(reader);
            EnableLight4 = ReadBool(reader);
        }
    }
}
