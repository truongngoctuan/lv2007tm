using System;
using System.Collections.Generic;
using System.IO;
using Microsoft.Xna.Framework;
using Microsoft.Xna.Framework.Graphics;

namespace _3DPresentation.Models.PointModel
{
    public class PointModel
    {
        PointManager pointManager;
        public Matrix WorldMatrix { get; set; }
        public bool IsVisible = true;
        private PointModel()
        {
            pointManager = new PointManager();
            WorldMatrix = Matrix.Identity;
        }

        public static PointModel Import(FileInfo file)
        {
            PointModel pointModel = null;
            if (file.Extension.ToLower() == ".ply")
            {
                using(StreamReader sr = file.OpenText())
                {
                    string ss = sr.ReadLine();
                    try
                    {
                        string temp = "element vertex";
                        while (!ss.Contains(temp))
                            ss = sr.ReadLine();
                        
                        ss = ss.Substring(temp.Length);
                        int nPoints = int.Parse(ss);

                        while (!ss.Contains("end_header"))
                            ss = sr.ReadLine();

                        pointModel = Import_PLY(sr, nPoints); 
                    }
                    catch (IOException io)
                    {
                    }
                }
            }
            return pointModel;
        }

        public static PointModel Import_PLY(StreamReader sr, int nPoints)
        {
            PointModel pointModel = new PointModel();
            pointModel.pointManager.Begin(nPoints);
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

                pointModel.pointManager.AddPoint(new Vector3(x, y, z), Color.FromNonPremultiplied(r, g, b, a));
            }
            pointModel.pointManager.End();
            return pointModel;
        }

        public void InitBuffers(GraphicsDevice graphicsDevice)
        {
            pointManager.InitBuffers(graphicsDevice);
        }

        public void Render(GraphicsDevice graphicsDevice)
        {
            for (int partitionIndex = 0; partitionIndex < pointManager.Partitions.Count; partitionIndex++)
            //for (int partitionIndex = 0; partitionIndex < 1; partitionIndex++)
            {
                pointManager.RenderPartition(graphicsDevice, partitionIndex);
            }
        }
    }
}
