﻿using Microsoft.Xna.Framework.Graphics;
using Microsoft.Xna.Framework;
using _3DPresentation.Models;
using _3DPresentation.Effects;
using System.ComponentModel;
using System.IO;
using System;

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
            else if (line == "TextureMaterial")
            {
                TextureMaterial material = new TextureMaterial();
                material.LoadMaterial(reader);
                return material;
            }

            else if (line == "NoEffectMaterial")
            {
                SimpleEffectMaterial material = new SimpleEffectMaterial();
                material.LoadMaterial(reader);
                return material;
            }
            else if (line == "TexturedMaterial")
            {
                TexturedNoEffectMaterial material = new TexturedNoEffectMaterial();
                material.LoadMaterial(reader);
                return material;
            }
            else if (line == "VertexColorMaterial")
            {
                VertexColorMaterial material = new VertexColorMaterial();
                material.LoadMaterial(reader);
                return material;
            }
            else if (line == "FourPointLightsTextureMaterial")
            {
                FourPointLightsTextureMaterial material = new FourPointLightsTextureMaterial();
                material.LoadMaterial(reader);
                return material;
            }


            else if (line == "PointMaterial")
            {
                PointMaterial material = new PointMaterial();
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
            if (items.Length < 3)
                return GlobalVars.ColorEnum.Transparent;
            int r = int.Parse(items[0]);
            int g = int.Parse(items[1]);
            int b = int.Parse(items[2]);
            return GlobalVars.GetColorEnum(r, g, b);
        }
        protected static bool SaveTexture(string texturePath, string textureName)
        {
            string filePath = string.Format("{0}/{1}", texturePath, textureName);
            return ResourceManager.SaveBitmap(textureName, filePath);
        }

        public override string ToString()
        {
            Type type = this.GetType();
            return type.Name;
        }

        public static string GetName(Type type)
        {
            if (type == typeof(BasicMaterial))
                return "BasicMaterial";
            else if (type == typeof(FourPointLightsMaterial))
                return "FourPointLightsMaterial";
            else if (type == typeof(SimpleEffectMaterial))
                return "NoEffectMaterial";
            else if (type == typeof(PointMaterial))
                return "PointMaterial";
            else if (type == typeof(TexturedNoEffectMaterial))
                return "TexturedMaterial";
            else if (type == typeof(VertexColorMaterial))
                return "VertexColorMaterial";
            else if (type == typeof(TextureMaterial))
                return "TextureMaterial";
            else if (type == typeof(FourPointLightsTextureMaterial))
                return "FourPointLightsTextureMaterial";
            return "Material";
        }

        #region INotifyPropertyChanged Members

        public event PropertyChangedEventHandler PropertyChanged;

        #endregion
    }
}