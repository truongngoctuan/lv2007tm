using System;
using System.Windows;
using System.Windows.Controls;
using System.Windows.Media.Animation;
using Microsoft.Xna.Framework.Graphics;
using Microsoft.Xna.Framework;
using System.IO;
using Babylon;
using System.Threading;

namespace _3DPresentation.Models
{
    public abstract class BaseModel
    {
        public enum Type { XYZ, XYZ_RGB, XYZ_NORMAL, XYZ_RGB_NORNAL };

        // state
        public bool IsEnabled { get; set; }
        public bool IsLoaded { get; protected set; }
        public bool IsInitialized { get; protected set; }

        public CustomBoundingInfo BoundingInfo { get; set; }
        public float Scale { get; set; }     

        // position        
        Vector3 position;
        Vector3 rotation;
        Matrix worldMatrix;
        public Vector3 Position
        {
            get { return position; }
            set { position = value; UpdateMatrix(); }
        }
        public Vector3 Rotation
        {
            get { return rotation; }
            set { rotation = value; UpdateMatrix(); }
        }
        public Matrix WorldMatrix
        {
            get { return worldMatrix; }
        }
        private void UpdateMatrix()
        {
            worldMatrix = Matrix.Identity;
            worldMatrix *= Matrix.CreateFromYawPitchRoll(rotation.Y, rotation.X, rotation.Z);
            worldMatrix *= Matrix.CreateTranslation(position.X, position.Y, position.Z);

            BoundingInfo.UpdateWorldDatas(worldMatrix, Scale);
        }

        public BaseModel()
        {
            position = Vector3.Zero;
            rotation = Vector3.Zero;
            worldMatrix = Matrix.Identity;
            Scale = 1.0f;

            IsEnabled = true;
            IsLoaded = false;
        }

        public void InitBoundingBox(Vector3[] points)
        {
            BoundingInfo = new CustomBoundingInfo(points);
        }

        public static BaseModel Import(FileInfo file)
        {
            BaseModel model = null;
            if (file.Extension.ToLower() == ".ply")
            {
                using (StreamReader sr = file.OpenText())
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
                                if (ss.Contains(rgb_header))
                                    rgb = true;
                                else if (ss.Contains(normal_header))
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

                        model = BaseModel.Import_PLY(sr, nPoints, nFaces, type);
                    }
                    catch (IOException io)
                    {
                        model = null;
                    }
                }
            }
            return model;
        }
        private static BaseModel Import_PLY(StreamReader sr, int nPoints, int nFaces, Type type)
        {
            if (nPoints == 0)
                return null;
            if (sr == null)
                return null;

            BaseModel model = null;
            if (nFaces > 0)
                model = new FaceModel();
            else
                model = new PointModel();

            model.IsLoaded = false;
            model.Begin(nPoints, nFaces);

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

                    model.AddVertex(new Vector3(x, y, z), GlobalVars.White);                    
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

                    model.AddVertex(new Vector3(x, y, z), Color.FromNonPremultiplied(r, g, b, a));
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

                model.AddIndice(i1, i2, i3);
            }

            model.End();
            model.IsLoaded = true;            
            return model;
        }

        Vector3[] points; int iPoint = 0;
        public virtual void Begin(int nPoints, int nFaces)
        {
            points = new Vector3[nPoints];
        }
        public virtual void AddVertex(Vector3 position, Color color)
        {
            points[iPoint++] = position;
        }
        public virtual void AddIndice(int i1, int i2, int i3)
        {
            // do nothing
        }
        public virtual void End()
        {
            InitBoundingBox(points);
            points = null;
        }
        public abstract void InitBuffers(GraphicsDevice graphicsDevice);

        private Thread oThread;
        public virtual void Render(GraphicsDevice graphicsDevice)
        {
            if (IsInitialized == false)
            {
                if (oThread == null)
                {
                    oThread = new Thread(this.DoWork);
                    oThread.Start(graphicsDevice);
                }
                else if(!oThread.IsAlive)
                {
                    oThread = null;
                    //oThread.Abort();
                    oThread = new Thread(this.DoWork);
                    oThread.Start(graphicsDevice);
                }
            }

            // derived class render here
        }

        public void DoWork(object data)
        {
            if (data is GraphicsDevice)
            {
                InitBuffers((GraphicsDevice)data);
                IsInitialized = true;
            }
        }

        public void Reload()
        {
            IsInitialized = false;
        }
    }
}
