using System;
using System.Collections.Generic;
using System.IO;
using Microsoft.Xna.Framework;
using Microsoft.Xna.Framework.Graphics;

namespace _3DPresentation.Models.FaceModel
{
    public class FaceModel
    {
        public enum Type { XYZ, XYZ_RGB, XYZ_NORMAL, XYZ_RGB_NORNAL };
        FaceManager pointManager;
        public Matrix WorldMatrix { get; set; }
        public bool IsVisible = true;
        private FaceModel()
        {
            pointManager = new FaceManager();
            WorldMatrix = Matrix.Identity;
        }

        public static FaceModel Import(FileInfo file)
        {
            FaceModel pointModel = null;
            if (file.Extension.ToLower() == ".ply")
            {
                using(StreamReader sr = file.OpenText())
                {                    
                    string numVertex = "element vertex";
                    string numFace = "element face";
                    string property = "property";
                    string rgb_header = "red";
                    string normal_header = "nx";
                    bool rgb = false;
                    bool normal = false;
                    int nPoints = 0;
                    int nFaces = 0;
                    Type type = Type.XYZ;
                    try
                    {
                        string ss = sr.ReadLine();
                        while (!ss.Contains("end_header"))
                        {
                            if (ss.Contains(numVertex))
                            {
                                ss = ss.Substring(numVertex.Length);
                                nPoints = int.Parse(ss);
                            }
                            else if (ss.Contains(property))
                            {
                                if(ss.Contains(rgb_header))
                                    rgb = true;
                                else if(ss.Contains(normal_header))
                                    normal = true;
                            }
                            else if (ss.Contains(numFace))
                            {
                                ss = ss.Substring(numFace.Length);
                                nFaces = int.Parse(ss);
                            }
                            ss = sr.ReadLine();
                        }

                        if (rgb && normal)
                            type = Type.XYZ_RGB_NORNAL;
                        else if (rgb)
                            type = Type.XYZ_RGB;
                        else if (normal)
                            type = Type.XYZ_NORMAL;

                        pointModel = Import_PLY(sr, nPoints, nFaces, type); 
                    }
                    catch (IOException io)
                    {
                        pointModel = null;
                    }
                }
            }
            return pointModel;
        }

        public static FaceModel Import_PLY(StreamReader sr, int nPoints, int nFaces, Type type)
        {
            FaceModel faceModel = new FaceModel();
            faceModel.pointManager.Begin(nPoints, nFaces);

            if (type == Type.XYZ)
            {
                for (int i = 0; i < nPoints; i++)
                {
                    string ss = sr.ReadLine();
                    string[] Items = ss.Split(new char[] { ' ' });

                    if (Items.Length < 3)
                        continue;

                    float x = Convert.ToSingle(Items[0]);
                    float y = Convert.ToSingle(Items[1]);
                    float z = Convert.ToSingle(Items[2]);

                    faceModel.pointManager.AddPoint(new Vector3(x, y, z), GlobalVars.White);
                }
            }
            else if (type == Type.XYZ_RGB)
            {
                for (int i = 0; i < nPoints; i++)
                {
                    string ss = sr.ReadLine();
                    string[] Items = ss.Split(new char[] { ' ' });

                    if (Items.Length < 6)
                        continue;

                    float x = Convert.ToSingle(Items[0]);
                    float y = Convert.ToSingle(Items[1]);
                    float z = Convert.ToSingle(Items[2]);
                    int r = Convert.ToInt32(Items[3]);
                    int g = Convert.ToInt32(Items[4]);
                    int b = Convert.ToInt32(Items[5]);
                    int a = 255;

                    faceModel.pointManager.AddPoint(new Vector3(x, y, z), Color.FromNonPremultiplied(r, g, b, a));
                }
            }
            else if (type == Type.XYZ_NORMAL)
            {
            }
            else if (type == Type.XYZ_RGB_NORNAL)
            {
            }
            

            for (int i = 0; i < nFaces; i++)
            {
                string ss = sr.ReadLine();
                string[] Items = ss.Split(new char[] { ' ' });

                if (Items.Length < 4)
                    continue;

                int i1 = Convert.ToInt32(Items[1]);
                int i2 = Convert.ToInt32(Items[2]);
                int i3 = Convert.ToInt32(Items[3]);

                faceModel.pointManager.AddIndice(i1, i2, i3);
            }

            faceModel.pointManager.End();
            return faceModel;
        }

        public void InitBuffers(GraphicsDevice graphicsDevice)
        {
            pointManager.InitBuffers(graphicsDevice);
        }

        public void Render(GraphicsDevice graphicsDevice)
        {
            for (int partitionIndex = 0; partitionIndex < pointManager.Partitions.Count; partitionIndex++)
            //for (int partitionIndex = 0; partitionIndex < 5; partitionIndex++)
            {
                pointManager.RenderPartition(graphicsDevice, partitionIndex);
            }
        }
    }
}
