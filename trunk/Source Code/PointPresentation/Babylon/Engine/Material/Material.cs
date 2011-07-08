using System.IO;
using Microsoft.Xna.Framework.Graphics;

namespace Babylon
{
    public abstract class Material : RootElement
    {
        CullMode cullMode = CullMode.CullCounterClockwiseFace;
        FillMode fillMode = FillMode.Solid;
        float alpha = 1.0f;
        bool hasTextureAlpha;

        public bool HasTextureAlpha
        {
            get { return hasTextureAlpha; }
            protected set
            {
                hasTextureAlpha = value;
            }
        }

        public virtual bool IsOpacity
        {
            get { return false; }
        }

        public bool HasAlpha
        {
            get { return hasTextureAlpha || alpha < 1.0f; }
        }

        public Scene Scene { get; private set; }
        public Engine Engine { get; private set; }

        public CullMode CullMode
        {
            get { return cullMode; }
            set { cullMode = value; }
        }

        public FillMode FillMode
        {
            get { return fillMode; }
            set { fillMode = value; }
        }

        public float Alpha
        {
            get { return alpha; }
            set { alpha = value; }
        }

        protected Material(string name, Scene scene)
            : base(name)
        {
            Scene = scene;
            Scene.Materials.Add(this);

            Engine = scene.Engine;
        }

        public abstract void Render(SubModel subObject);

        internal virtual Material GetEffectiveMaterial(int materialID)
        {
            return this;
        }

        public override void Dispose()
        {
        }
    }
}
