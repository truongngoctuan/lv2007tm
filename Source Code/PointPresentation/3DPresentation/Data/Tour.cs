using System;
using System.Net;
using System.Windows;
using System.Windows.Controls;
using System.Windows.Documents;
using System.Windows.Ink;
using System.Windows.Input;
using System.Windows.Media;
using System.Windows.Media.Animation;
using System.Windows.Shapes;
using System.IO;
using _3DPresentation.Models;
using System.Collections.Generic;
using Microsoft.Xna.Framework;
using _3DPresentation.Material;
using _3DPresentation.Effects;

namespace _3DPresentation.Data
{
    public class Tour
    {
        public string Name;
        public string SceneName;
        public BaseModel[] Models;

        public Tour()
        {
            EffectManager.InitEffects();
            ResourceManager.Init();
        }

        public bool Save()
        {
            bool result = true;
            string storeDirectory = Utils.Global.GetRealTourStorePath();
            string tourFileDir = string.Format("{0}/{1}/", storeDirectory, Name);
            string tourFilePath = string.Format("{0}/{1}/{1}.tour", storeDirectory, Name);
            FileInfo tourFile = Utils.Global.GetRealFile(tourFilePath);
            using (StreamWriter writer = new StreamWriter(tourFile.OpenWrite()))
            {
                writer.WriteLine(Name);
                writer.WriteLine(SceneName);
                writer.WriteLine(Models.Length);
                for (int i = 0; i < Models.Length; i++)
                {
                    writer.WriteLine(Models[i].Name);
                    writer.WriteLine(string.Format("{0}", Models[i].Scale));
                    writer.WriteLine(string.Format("{0} {1} {2}", Models[i].Rotation.X, Models[i].Rotation.Y, Models[i].Rotation.Z));
                    writer.WriteLine(string.Format("{0} {1} {2}", Models[i].Position.X, Models[i].Position.Y, Models[i].Position.Z));                    
                    
                    FileInfo modelFile = Utils.Global.GetRealFile(tourFileDir + "Models/" + Models[i].Name + ".ply");
                    Models[i].Export(BaseModel.FileType.PLY, Models[i].Type, modelFile, true);
                    Models[i].Material.Save(writer, string.Format("{0}/Models/", tourFileDir, Models[i].Name));
                }
                writer.Close();
            }            
            return result;
        }
        public static Tour Load(string name)
        {
            Tour tour = null;
            string storeDirectory = Utils.Global.GetRealTourStorePath();
            string tourFileDir = string.Format("{0}/{1}/", storeDirectory, name);
            string tourFilePath = string.Format("{0}/{1}/{1}.tour", storeDirectory, name);
            FileInfo tourFile = Utils.Global.GetFileInfo(tourFilePath);
            if (tourFile.Exists)
            {
                tour = new Tour();
                using (StreamReader reader = new StreamReader(tourFile.OpenRead()))
                {
                    tour.Name = reader.ReadLine();
                    tour.SceneName = reader.ReadLine();

                    int nModels = Convert.ToInt32(reader.ReadLine());                    
                    string modelName;
                    string line;
                    string[] items;
                    float positionX, positionY, positionZ;
                    float rotationX, rotationY, rotationZ;
                    float scale;
                    BaseModel model = null;
                    FileInfo modelFile;

                    tour.Models = new BaseModel[nModels];
                    for (int i = 0; i < nModels; i++)
                    {
                        modelName = reader.ReadLine();

                        line = reader.ReadLine();
                        scale = Convert.ToSingle(line);

                        line = reader.ReadLine();
                        items = line.Split(new char[] { ' ' });
                        rotationX = Convert.ToSingle(items[0]);
                        rotationY = Convert.ToSingle(items[1]);
                        rotationZ = Convert.ToSingle(items[2]);

                        line = reader.ReadLine();
                        items = line.Split(new char[] { ' ' });
                        positionX = Convert.ToSingle(items[0]);
                        positionY = Convert.ToSingle(items[1]);
                        positionZ = Convert.ToSingle(items[2]);

                        modelFile = Utils.Global.GetFileInfo(tourFileDir + "Models/" + modelName + ".ply");
                        if(modelFile.Exists)
                        {
                            model = BaseModel.Import(modelFile);
                            model.Name = modelName;
                            model.Scale = scale;
                            model.Rotation = new Vector3(rotationX, rotationY, rotationZ);
                            model.Position = new Vector3(positionX, positionY, positionZ);                           
                            
                            model.Material = BaseMaterial.Load(reader);
                            tour.Models[i] = model;
                        }                        
                    }
                    reader.Close();
                }
            }                
            return tour;
        }
    }
}
