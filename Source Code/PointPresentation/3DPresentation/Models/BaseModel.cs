using System;
using System.Windows;
using System.Windows.Controls;
using System.Windows.Media.Animation;
using Microsoft.Xna.Framework.Graphics;
using Microsoft.Xna.Framework;
using System.IO;
using Babylon;
using System.Threading;
using _3DPresentation.Material;

namespace _3DPresentation.Models
{
    public abstract class BaseModel
    {
        public enum VertexType { XYZ, XYZ_RGB, XYZ_NORMAL, XYZ_RGB_NORNAL };
        public enum FileType { PLY };

        // state
        public bool IsEnabled { get; set; }
        public bool IsLoaded { get; protected set; }
        public bool IsInitialized { get; protected set; }

        public CustomBoundingInfo BoundingInfo { get; set; }

        // material
        private BaseMaterial material;
        public BaseMaterial Material
        {
            get
            {
                if (material == null)
                    material = GetDefaultMaterial();
                return material;
            }
            set
            {
                material = value;
            }
        }
        private BaseMaterial specialMaterial;
        public BaseMaterial SpecialMaterial
        {
            get
            {
                if (specialMaterial == null)
                    specialMaterial = GetDefaultSpecialMaterial();
                return specialMaterial;
            }
            set
            {
                specialMaterial = value;
            }
        }

        // position
        float scale;
        Vector3 position;
        Vector3 rotation;
        Matrix worldMatrix;
        public float Scale
        {
            get { return scale; }
            set { scale = value; UpdateMatrix(); }
        }
        public Vector3 Position
        {
            get { return position; }
            set { position = value; //UpdateMatrix(); 
                UpdateMatrix2(); }
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
            worldMatrix *= Matrix.CreateScale(Scale);
            worldMatrix *= Matrix.CreateTranslation(-BoundingInfo.BoundingSphere.Center.X, -BoundingInfo.BoundingSphere.Center.Y, -BoundingInfo.BoundingSphere.Center.Z);
            worldMatrix *= Matrix.CreateFromYawPitchRoll(rotation.Y, rotation.X, rotation.Z);
            worldMatrix *= Matrix.CreateTranslation(BoundingInfo.BoundingSphere.Center.X, BoundingInfo.BoundingSphere.Center.Y, BoundingInfo.BoundingSphere.Center.Z);
            worldMatrix *= Matrix.CreateTranslation(position.X, position.Y, position.Z);

            BoundingInfo.UpdateWorldDatas(worldMatrix, Scale);
        }

        Matrix rotationMatrix = Matrix.Identity;

        public Matrix RotationMatrix
        {
            get { return rotationMatrix; }
            set { rotationMatrix = value; UpdateMatrix2(); }
        }

        private void UpdateMatrix2()
        {
            worldMatrix = Matrix.Identity;
            worldMatrix *= Matrix.CreateScale(Scale);
            worldMatrix *= Matrix.CreateTranslation(-BoundingInfo.BoundingSphere.Center.X, -BoundingInfo.BoundingSphere.Center.Y, -BoundingInfo.BoundingSphere.Center.Z);
            worldMatrix *= rotationMatrix;
            worldMatrix *= Matrix.CreateTranslation(BoundingInfo.BoundingSphere.Center.X, BoundingInfo.BoundingSphere.Center.Y, BoundingInfo.BoundingSphere.Center.Z);
            worldMatrix *= Matrix.CreateTranslation(position.X, position.Y, position.Z);

            BoundingInfo.UpdateWorldDatas(worldMatrix, Scale);
        }


        public BaseModel()
        {
            position = Vector3.Zero;
            rotation = Vector3.Zero;
            worldMatrix = Matrix.Identity;
            scale = 1.0f;

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
                    VertexType vertexType = VertexType.XYZ;
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
                            vertexType = VertexType.XYZ_RGB_NORNAL;
                        else if (rgb)
                            vertexType = VertexType.XYZ_RGB;
                        else if (normal)
                            vertexType = VertexType.XYZ_NORMAL;

                        model = BaseModel.Import_PLY(sr, nPoints, nFaces, vertexType);
                    }
                    catch (IOException io)
                    {
                        model = null;
                    }
                }
            }
            return model;
        }
        private static BaseModel Import_PLY(StreamReader sr, int nPoints, int nFaces, VertexType vertexType)
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

            if (vertexType == VertexType.XYZ)
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
            else if (vertexType == VertexType.XYZ_RGB)
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
            else if (vertexType == VertexType.XYZ_NORMAL)
            {
            }
            else if (vertexType == VertexType.XYZ_RGB_NORNAL)
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
            model.NumPoints = nPoints;
            model.NumFaces = nFaces;
            model.Type = vertexType; 
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
        public virtual void Render(GraphicsDevice graphicsDevice, bool specialRender = false)
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
            if (specialRender)
            {
                SpecialMaterial.Apply();
            }
            else
            {
                Material.Apply();
            }
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

        public string Name { get; set; }
        public VertexType Type;
        public long NumPoints;
        public long NumFaces;

        private static bool WriteHeader(FileType fileType, VertexType vertexType, long nPoints, long nFaces, StreamWriter writer)
        {
            bool result = false;
            if (fileType == FileType.PLY && writer != null)
            {
                writer.WriteLine("ply");
                writer.WriteLine("format ascii 1.0");
                writer.WriteLine("element vertex " + nPoints);

                if (vertexType == VertexType.XYZ)
                {
                    writer.WriteLine("property float32 x");
                    writer.WriteLine("property float32 y");
                    writer.WriteLine("property float32 z");
                }
                else if (vertexType == VertexType.XYZ_RGB)
                {
                    writer.WriteLine("property float32 x");
                    writer.WriteLine("property float32 y");
                    writer.WriteLine("property float32 z");
                    writer.WriteLine("property uchar red");
                    writer.WriteLine("property uchar green");
                    writer.WriteLine("property uchar blue");
                }
                else if (vertexType == VertexType.XYZ_RGB_NORNAL)
                {
                    writer.WriteLine("property float32 x");
                    writer.WriteLine("property float32 y");
                    writer.WriteLine("property float32 z");
                    writer.WriteLine("property uchar red");
                    writer.WriteLine("property uchar green");
                    writer.WriteLine("property uchar blue");
                    writer.WriteLine("property float32 nx");
                    writer.WriteLine("property float32 ny");
                    writer.WriteLine("property float32 nz");
                }
                else
                {
                    return false;
                }
                writer.WriteLine("element face " + nFaces);                
                writer.WriteLine("end_header");
                result = true;
            }
            return result;
        }

        public bool Export(FileType fileType, VertexType vertexType, FileInfo file)
        {
            bool result = false;
            using (StreamWriter writer = new StreamWriter(file.OpenWrite()))
            {
                if (result = WriteHeader(fileType, vertexType, NumPoints, NumFaces, writer))
                {
                    result = Export(fileType, vertexType, writer);
                }
            }
            return result;
        }        

        public bool ExportAll(VertexType vertexType, BaseModel[] models, string batchName, FileType fileType)
        {
            bool result = true;
            string storeDirectory = Utils.Global.GetRealModelStoreDirectory();
            for (int i = 0; i < models.Length; i++)
            {
                if (fileType == FileType.PLY)
                {
                    FileInfo file = Utils.Global.GetRealFile(storeDirectory + batchName + '/' + models[i].Name + ".ply");
                    if (models[i].Export(fileType, vertexType, file) == false)
                        result = false;
                }
            }
            return result;
        }

        public bool ExportUnitedModel(FileType fileType, VertexType vertexType, BaseModel[] models, string batchName)
        {            
            string storeDirectory = Utils.Global.GetRealModelStoreDirectory();
            FileInfo file = Utils.Global.GetRealFile(storeDirectory + batchName + ".ply");

            long nPoints = 0;
            long nFaces = 0;
            for (int i = 0; i < models.Length; i++)
            {
                nPoints += models[i].NumPoints;
                nFaces += models[i].NumFaces;
            }

            bool result = true;
            using (StreamWriter writer = new StreamWriter(file.OpenWrite()))
            {
                if (result = WriteHeader(fileType, VertexType.XYZ_RGB, NumPoints, NumFaces, writer))
                {
                    for (int i = 0; i < models.Length; i++)
                    {
                        if (fileType == FileType.PLY)
                        {
                            if (models[i].ExportVertexData(fileType, vertexType, writer) == false)
                                result = false;
                        }
                    }

                    if (result)
                    {
                        long offset = 0;
                        for (int i = 0; i < models.Length; i++)
                        {
                            if (fileType == FileType.PLY)
                            {
                                if (models[i].ExportIndiceData(fileType, vertexType, writer, offset) == false)
                                    result = false;
                            }
                            offset += models[i].NumPoints;
                        }
                    }
                }
            }
            return result;
        }

        protected bool Export(FileType fileType, VertexType vertexType, StreamWriter writer)
        {
            if (fileType == FileType.PLY)
            {
                if (ExportVertexData(fileType, vertexType, writer) == false)
                    return false;
                if (ExportIndiceData(fileType, vertexType, writer) == false)
                    return false;
            }
            return true;
        }
        protected abstract bool ExportVertexData(FileType fileType, VertexType vertexType, StreamWriter writer);
        protected abstract bool ExportIndiceData(FileType fileType, VertexType vertexType, StreamWriter writer, long offset = 0);
        protected abstract BaseMaterial GetDefaultMaterial();
        protected abstract BaseMaterial GetDefaultSpecialMaterial();
    }
}
