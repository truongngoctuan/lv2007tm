using Microsoft.Xna.Framework;
using Microsoft.Xna.Framework.Graphics;
using Babylon.Toolbox;
using System;

namespace _3DPresentation.Effects
{
    public class FourPointLights : Effect
    {
        readonly EffectParameter WorldParameter;
        readonly EffectParameter WorldViewProjectionParameter;

        readonly EffectParameter LightSource1Parameter;        
        readonly EffectParameter LightColor1Parameter;

        readonly EffectParameter LightSource2Parameter;
        readonly EffectParameter LightColor2Parameter;

        readonly EffectParameter LightSource3Parameter;
        readonly EffectParameter LightColor3Parameter;

        readonly EffectParameter LightSource4Parameter;
        readonly EffectParameter LightColor4Parameter;

        readonly EffectParameter EnableLightsParameter;
        readonly EffectParameter AmbientLightParameter;

        public FourPointLights(GraphicsDevice device)
            : this(device, "3DPresentation", "Effects/FourPointLights/FourPointLights")
        {
        }

        protected FourPointLights(GraphicsDevice device, string assemblyName, string rootName)
            : base(device, assemblyName, rootName)
        {
            WorldParameter = GetParameter("World");    
            WorldViewProjectionParameter = GetParameter("WorldViewProjection");

            LightSource1Parameter = GetParameter("LightSource1");
            LightColor1Parameter = GetParameter("LightColor1");

            LightSource2Parameter = GetParameter("LightSource2");
            LightColor2Parameter = GetParameter("LightColor2");

            LightSource3Parameter = GetParameter("LightSource3");
            LightColor3Parameter = GetParameter("LightColor3");

            LightSource4Parameter = GetParameter("LightSource4");
            LightColor4Parameter = GetParameter("LightColor4");

            EnableLightsParameter = GetParameter("EnableLights");
            AmbientLightParameter = GetParameter("AmbientLight");            
        }

        public string Name { get; set; }
        public Matrix World { get; set; }
        public Matrix View { get; set; }
        public Matrix Projection { get; set; }

        public Vector3 LightSource1 { get; set; }        
        public Color LightColor1 { get; set; }
        public bool EnableLight1{ get; set; }

        public Vector3 LightSource2 { get; set; }
        public Color LightColor2 { get; set; }
        public bool EnableLight2 { get; set; }

        public Vector3 LightSource3 { get; set; }
        public Color LightColor3 { get; set; }
        public bool EnableLight3 { get; set; }

        public Vector3 LightSource4 { get; set; }
        public Color LightColor4 { get; set; }
        public bool EnableLight4 { get; set; }

        public Color AmbientLight { get; set; }

        public override void Apply()
        {
            WorldParameter.SetValue(World);
            WorldViewProjectionParameter.SetValue(World * View * Projection);

            if (EnableLight1)
            {
                LightSource1Parameter.SetValue(LightSource1.X, LightSource1.Y, LightSource1.Z, 0.0f);
                LightColor1Parameter.SetValue(LightColor1);
            }

            if (EnableLight2)
            {
                LightSource2Parameter.SetValue(LightSource2.X, LightSource2.Y, LightSource2.Z, 0.0f);
                LightColor2Parameter.SetValue(LightColor2);
            }

            if (EnableLight3)
            {
                LightSource3Parameter.SetValue(LightSource3.X, LightSource3.Y, LightSource3.Z, 0.0f);
                LightColor3Parameter.SetValue(LightColor3);
            }

            if (EnableLight4)
            {
                LightSource4Parameter.SetValue(LightSource4.X, LightSource4.Y, LightSource4.Z, 0.0f);
                LightColor4Parameter.SetValue(LightColor4);
            }

            EnableLightsParameter.SetValue(Convert.ToSingle(EnableLight1), Convert.ToSingle(EnableLight2), Convert.ToSingle(EnableLight3), Convert.ToSingle(EnableLight4));
            AmbientLightParameter.SetValue(AmbientLight);
            base.Apply();
        }

        public override string ToString()
        {
            return Name;
        }

        public override void Dispose()
        {
            base.Dispose();
        }
    }
}
