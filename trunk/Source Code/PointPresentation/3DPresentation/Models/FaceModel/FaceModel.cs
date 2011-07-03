using System;
using System.Collections.Generic;
using System.IO;
using Microsoft.Xna.Framework;
using Microsoft.Xna.Framework.Graphics;

namespace _3DPresentation.Models.FaceModel
{
    public class FaceModel
    {
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
                    int nPoints = 0;
                    int nFaces = 0;
                    try
                    {
                        string ss = sr.ReadLine();
                        while (!ss.Contains("end_header"))
                        {
                            if (ss.Contains("element vertex"))
                            {
                                ss = ss.Substring(numVertex.Length);
                                nPoints = int.Parse(ss);
                            }
                            else if (ss.Contains("element face"))
                            {
                                ss = ss.Substring(numFace.Length);
                                nFaces = int.Parse(ss);
                            }
                            ss = sr.ReadLine();
                        }
                        pointModel = Import_PLY(sr, nPoints, nFaces); 
                    }
                    catch (IOException io)
                    {
                        pointModel = null;
                    }
                }
            }
            return pointModel;
        }

        public static FaceModel Import_PLY(StreamReader sr, int nPoints, int nFaces)
        {
            FaceModel faceModel = new FaceModel();
            faceModel.pointManager.Begin(nPoints, nFaces);
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
