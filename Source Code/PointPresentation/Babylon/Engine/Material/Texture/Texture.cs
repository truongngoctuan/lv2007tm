using Microsoft.Xna.Framework;
using Microsoft.Xna.Framework.Graphics;

namespace Babylon
{
    public partial class Texture : RootElement
    {
        readonly Scene scene;
        LoadedTexture loadedTexture;
        TextureAddressMode uAddressMode = TextureAddressMode.Wrap;
        TextureAddressMode vAddressMode = TextureAddressMode.Wrap;

        public bool HasAlpha { get; set; }

        public bool HasTextureData
        {
            get
            {
                if (loadedTexture == null)
                    return false;
                if (loadedTexture.StreamingState != StreamingState.Loaded)
                {
                    if (loadedTexture.StreamingState == StreamingState.PreLoaded)
                    {
                        scene.RegisterForStreaming(loadedTexture);
                    }
                    return false;
                }
                return true;
            }
        }

        public Texture2D Texture2D
        { 
            get
            {
                if (loadedTexture == null)
                    return null;
                return loadedTexture.Texture2D;
            }
        }

        public float Level { get; set; }

        public int MapCoordinatesIndex { get; set; }

        public float UAng { get; set; }

        public float VAng { get; set; }

        public float WAng { get; set; }

        public float UOffset { get; set; }

        public float VOffset { get; set; }

        public float UScale { get; set; }

        public float VScale { get; set; }

        public bool NeedInverseY { get; set; }

        public TextureAddressMode UAddressMode
        {
            get { return uAddressMode; }
            set { uAddressMode = value; }
        }

        public TextureAddressMode VAddressMode
        {
            get { return vAddressMode; }
            set { vAddressMode = value; }
        }

        public Texture(string name, Scene scene) : base(name)
        {
            this.scene = scene;
        }

        public override void Dispose()
        {
            scene.Engine.ReleaseTexture(loadedTexture);
        }

        void PrepareRowForTextureGeneration(ref Vector3 t)
        {
            Matrix matRot = MatrixLeftHanded.CreateFromYawPitchRoll(VAng, UAng, WAng);

            t.X -= UOffset + 0.5f;
            t.Y -= VOffset + 0.5f;
            t.Z -= 0.5f;

            t = Vector3.Transform(t, matRot);

            if (UScale != 1.0f)
            {
                t.X *= UScale;
            }

            if (VScale != 1.0f)
            {
                t.Y *= VScale;
            }

            t.X += 0.5f;
            t.Y += 0.5f;
            t.Z += 0.5f;
        }

        public Matrix ComputeTextureMatrix()
        {
            Vector3 t0 = new Vector3(0, 0, 0);
            Vector3 t1 = new Vector3(1.0f, 0, 0);
            Vector3 t2 = new Vector3(0, 1.0f, 0);

            Matrix matTemp = Matrix.Identity;

            PrepareRowForTextureGeneration(ref t0);
            PrepareRowForTextureGeneration(ref t1);
            PrepareRowForTextureGeneration(ref t2);

            t1 -= t0;
            t2 -= t0;

            matTemp.M11 = t1.X; matTemp.M12 = t1.Y; matTemp.M13 = t1.Z;
            matTemp.M21 = t2.X; matTemp.M22 = t2.Y; matTemp.M23 = t2.Z;
            matTemp.M31 = t0.X; matTemp.M32 = t0.Y; matTemp.M33 = t0.Z;

            if (NeedInverseY)
            {
                Matrix invMatrix = Matrix.Identity;
                invMatrix.M22 = -1.0f;
                invMatrix.M32 = 1.0f;

                matTemp = matTemp * invMatrix;
            }

            return matTemp;
        }
    }
}