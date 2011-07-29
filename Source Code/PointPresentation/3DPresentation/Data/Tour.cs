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
            string storeDirectory = Utils.Global.TourStorePath;
            string tourFileDir = string.Format("{0}/{1}/", storeDirectory, Name);
            string tourFilePath = string.Format("{0}/{1}/{1}.tour", storeDirectory, Name);
            MemoryStream memStream = new MemoryStream();
            using (StreamWriter writer = new StreamWriter(memStream))
            {
                writer.WriteLine(Name);
                writer.WriteLine(SceneName);
                if (Models != null)
                {
                    writer.WriteLine(Models.Length);
                    for (int i = 0; i < Models.Length; i++)
                    {
                        writer.WriteLine(Models[i].Name);
                        writer.WriteLine(string.Format("{0}", Models[i].Scale));
                        writer.WriteLine(string.Format("{0} {1} {2}", Models[i].Rotation.X, Models[i].Rotation.Y, Models[i].Rotation.Z));
                        writer.WriteLine(string.Format("{0} {1} {2}", Models[i].Position.X, Models[i].Position.Y, Models[i].Position.Z));


                        MemoryStream modelStream = new MemoryStream();
                        using (StreamWriter modelWriter = new StreamWriter(modelStream))
                        {
                            Models[i].Export(BaseModel.FileType.PLY, Models[i].Type, modelWriter, true);

                            if (Models[i].DiffuseTexture != null)
                            {
                                string strTexture = string.Format("{0}/Models/{1}", tourFileDir, Models[i].DiffuseTexture);
                                ResourceManager.SaveBitmap(Models[i].DiffuseTexture, strTexture);
                            }

                            Models[i].Material.Save(writer, string.Format("{0}/Models/", tourFileDir, Models[i].Name));


                            string strFile = string.Format("{0}/Models/{1}.ply", tourFileDir, Models[i].Name);
                            Utils.Global.WriteTo(strFile, modelStream);
                        }
                    }
                }
                else
                    writer.WriteLine(0);

                writer.Flush();
                Utils.Global.WriteTo(tourFilePath, memStream);
            }
            return result;
        }
        public static Tour Load(string name)
        {
            Tour tour = null;
            string storeDirectory = Utils.Global.TourStorePath;
            string tourFileDir = string.Format("{0}/{1}", storeDirectory, name);
            string tourFilePath = string.Format("{0}/{1}/{1}.tour", storeDirectory, name);
            Stream stream = Utils.Global.GetStream(tourFilePath, FileMode.Open);
            if (stream != null)
            {
                tour = new Tour();
                using (StreamReader reader = new StreamReader(stream))
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

                        string strFile = string.Format("{0}/Models/{1}.ply", tourFileDir, modelName);
                        Stream modelStream = Utils.Global.GetStream(strFile, FileMode.Open);
                        if (modelStream != null)
                        {
                            model = BaseModel.Import(modelStream);
                            if (model.DiffuseTexture != null)
                            {
                                string strTexture = string.Format("{0}/Models/{1}", tourFileDir, model.DiffuseTexture);
                                Stream textureStream = Utils.Global.GetStream(strTexture, FileMode.Open);
                                ResourceManager.LoadTexture(textureStream, model.DiffuseTexture);
                                textureStream.Close();
                            }
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
                stream.Close();
            }

            return tour;
        }
    }
}
