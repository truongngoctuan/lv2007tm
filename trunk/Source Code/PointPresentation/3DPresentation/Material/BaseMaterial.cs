using Microsoft.Xna.Framework.Graphics;
using Microsoft.Xna.Framework;
using _3DPresentation.Models;
using _3DPresentation.Effects;
using System.ComponentModel;
using System.IO;

namespace _3DPresentation.Material
{
    public abstract class BaseMaterial : INotifyPropertyChanged
    {
        public Matrix World { get; set; }
        public GraphicsDevice Device { get; set; }

        public abstract void Apply();
        protected abstract void LoadMaterial(StreamReader reader);
        public abstract void Save(StreamWriter writer, string texturePath);
        public static BaseMaterial Load(StreamReader reader)
        {
            string line = reader.ReadLine().Trim();
            if (line == "BasicMaterial")
            { 
                BasicMaterial material = new BasicMaterial();
                material.LoadMaterial(reader);
                return material;
            }
            else if (line == "FourPointLightsMaterial")
            {
                FourPointLightsMaterial material = new FourPointLightsMaterial();
                material.LoadMaterial(reader);
                return material;
            }
            else if (line == "NoEffectMaterial")
            {
                NoEffectMaterial material = new NoEffectMaterial();
                material.LoadMaterial(reader);
                return material;
            }
            else if (line == "PointMaterial")
            {
                PointMaterial material = new PointMaterial();
                material.LoadMaterial(reader);
                return material;
            }
            else if (line == "TexturedMaterial")
            {
                TexturedMaterial material = new TexturedMaterial();
                material.LoadMaterial(reader);
                return material;
            }
            else if (line == "VertexColorMaterial")
            {
                VertexColorMaterial material = new VertexColorMaterial();
                material.LoadMaterial(reader);
                return material;
            }
            else if (line == "TextureMaterial")
            {
                TextureMaterial material = new TextureMaterial();
                material.LoadMaterial(reader);
                return material;
            }
            else if (line == "FourPointLightsTextureMaterial")
            {
                FourPointLightsTextureMaterial material = new FourPointLightsTextureMaterial();
                material.LoadMaterial(reader);
                return material;
            }
            return null;
        }

        public GlobalVars.ColorEnum ReadColor(System.IO.StreamReader reader)
        {
            string line = reader.ReadLine();
            return StringToColor(line);
        }

        public float ReadFloat(System.IO.StreamReader reader)
        {
            string line = reader.ReadLine();
            return float.Parse(line);
        }

        public bool ReadBool(System.IO.StreamReader reader)
        {
            string line = reader.ReadLine();
            return bool.Parse(line);
        }

        public Vector3 ReadVector3(System.IO.StreamReader reader)
        {
            string line = reader.ReadLine();
            string[] items = line.Split(' ');
            if (items.Length > 3)
            {
                return new Vector3(float.Parse(items[0]), float.Parse(items[1]), float.Parse(items[2]));
            }
            return Vector3.Zero;
        }

        protected string ColorToString(GlobalVars.ColorEnum color)
        {
            Color c = GlobalVars.GetColor(color);
            return string.Format("{0} {1} {2}", c.R, c.G, c.B);
        }
        protected GlobalVars.ColorEnum StringToColor(string line)
        {
            string[] items = line.Split(' ');
            return GlobalVars.ColorEnum.Black;
        }
        protected static bool SaveTexture(string texturePath, string textureName)
        {
            string filePath = string.Format("{0}/{1}", texturePath, textureName);
            return ResourceManager.SaveBitmap(textureName, filePath);
        }
        #region INotifyPropertyChanged Members

        public event PropertyChangedEventHandler PropertyChanged;

        #endregion
    }
}
