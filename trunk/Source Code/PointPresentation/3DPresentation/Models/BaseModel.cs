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
        public enum VertexTypes { XYZ, XYZ_RGB, XYZ_NORMAL, XYZ_RGB_NORNAL, XYZ_TEXCOORD, XYZ_NORMAL_TEXCOORD };
        public enum FileType { PLY };

        private object lockThis = new object();
        // state
        public bool IsEnabled { get; set; }
        public bool IsLoaded { get; protected set; }
        public bool IsInitialized { get; protected set; }

        public CustomBoundingInfo BoundingInfo { get; set; }

        // material
        public string DiffuseTexture;
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
                lock (lockThis)
                {
                    material = value;
                }
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
                lock (lockThis)
                {
                    specialMaterial = value;
                }
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

        public static BaseModel Import(Stream stream, FileType fileType)
        {
            BaseModel model = null;
            if (fileType == FileType.PLY)
            {
                using (StreamReader sr = new StreamReader(stream))
                {
                    string numVertex = "element vertex";
                    string numFace = "element face";                                                          
                   
                    int nPoints = 0;
                    int nFaces = 0;
                    VertexTypes vertexType = VertexTypes.XYZ;
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
                            else if (ss.Contains(numFace))
                            {
                                ss = ss.Substring(numFace.Length);
                                nFaces = int.Parse(ss);
                            }
                            ss = sr.ReadLine();
                        }
                        model = BaseModel.Import_PLY(sr, nPoints, nFaces, vertexType, null);
                    }
                    catch (IOException io)
                    {
                        model = null;
                    }
                    sr.Close();
                }
            }
            return model;
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
                    string texcoord_header = "texcoord";
                    string texture = "TextureFile";
                    string comment = "comment";

                    string textureName = null;
                    bool rgb = false;
                    bool normal = false;
                    bool texCoord = false;
                    int nPoints = 0;
                    int nFaces = 0;
                    VertexTypes vertexType = VertexTypes.XYZ;
                    try
                    {
                        string ss = sr.ReadLine();
                        while (!ss.Contains("end_header"))
                        {
                            if(ss.Contains(comment))
                            {
                                if(ss.Contains(texture))
                                {
                                    string[] items = ss.Split(' ');
                                    if(items.Length < 3)
                                        continue;
                                    textureName  = items[2];
                                    string path = string.Format("{0}/{1}", file.Directory.FullName, textureName);
                                    FileInfo textureFile = new FileInfo(path);

                                    // add this to resourcemanager, assign the textureName to DiffuseTexture
                                    // so the appropriate material can load it from resourcemanager
                                    ResourceManager.LoadTexture(textureFile, textureName);
                                }
                            }
                            else if (ss.Contains(numVertex))
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
                                else if (ss.Contains(texcoord_header))
                                    texCoord = true;
                            }
                            else if (ss.Contains(numFace))
                            {
                                ss = ss.Substring(numFace.Length);
                                nFaces = int.Parse(ss);
                            }
                            ss = sr.ReadLine();
                        }

                        if (rgb && normal)
                            vertexType = VertexTypes.XYZ_RGB_NORNAL;
                        else if (rgb)
                            vertexType = VertexTypes.XYZ_RGB;
                        else if (texCoord & normal)
                            vertexType = VertexTypes.XYZ_NORMAL_TEXCOORD;
                        else if (texCoord)
                            vertexType = VertexTypes.XYZ_TEXCOORD;                        
                        else if (normal)
                            vertexType = VertexTypes.XYZ_NORMAL;

                        model = BaseModel.Import_PLY(sr, nPoints, nFaces, vertexType, textureName);
                        model.Name = file.Name;
                    }
                    catch (IOException io)
                    {
                        model = null;
                    }
                    sr.Close();
                }
            }
            return model;
        }
        private static BaseModel Import_PLY(StreamReader sr, int nPoints, int nFaces, VertexTypes vertexType, string textureName)
        {
            if (nPoints == 0)
                return null;
            if (sr == null)
                return null;

            BaseModel model = null;
            if (vertexType == VertexTypes.XYZ_TEXCOORD || vertexType == VertexTypes.XYZ_NORMAL_TEXCOORD)
                model = new TexCoordModel();
            else if (nFaces > 0)
                model = new FaceModel();
            else
                model = new PointModel();

            model.IsLoaded = false;
            model.NumPoints = nPoints;
            model.NumFaces = nFaces;
            model.Type = vertexType; 
            model.Begin(nPoints, nFaces);

            if (vertexType == VertexTypes.XYZ)
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

                    model.AddVertex(new Vector3(x, y, z), GlobalVars.GetColor(GlobalVars.ColorEnum.White));
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
            }
            else if (vertexType == VertexTypes.XYZ_RGB)
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
            }
            else if (vertexType == VertexTypes.XYZ_NORMAL)
            {
            }
            else if (vertexType == VertexTypes.XYZ_RGB_NORNAL)
            {
            }
            else if (vertexType == VertexTypes.XYZ_TEXCOORD)
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

                    model.AddVertex(new Vector3(x, y, z));
                }

                for (int i = 0; i < nFaces; i++)
                {
                    string ss = sr.ReadLine();
                    string[] Items = ss.Split(new char[] { ' ' });

                    if (Items.Length < 11)
                        continue;

                    int i1 = Convert.ToInt32(Items[1]);
                    int i2 = Convert.ToInt32(Items[2]);
                    int i3 = Convert.ToInt32(Items[3]);

                    float texCoord1x = Convert.ToSingle(Items[5]); float texCoord1y = Convert.ToSingle(Items[6]);
                    float texCoord2x = Convert.ToSingle(Items[7]); float texCoord2y = Convert.ToSingle(Items[8]);
                    float texCoord3x = Convert.ToSingle(Items[9]); float texCoord3y = Convert.ToSingle(Items[10]);

                    model.AddIndice(i1, i2, i3, new Vector2(texCoord1x, texCoord1y), new Vector2(texCoord2x, texCoord2y), new Vector2(texCoord3x, texCoord3y));
                }
                model.DiffuseTexture = textureName;
            }
            else if (vertexType == VertexTypes.XYZ_NORMAL_TEXCOORD)
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
                    float nx = Convert.ToSingle(Items[3]);
                    float ny = Convert.ToSingle(Items[4]);
                    float nz = Convert.ToSingle(Items[5]);

                    model.AddVertex(new Vector3(x, y, z), new Vector3(nx, ny, nz));
                }

                for (int i = 0; i < nFaces; i++)
                {
                    string ss = sr.ReadLine();
                    string[] Items = ss.Split(new char[] { ' ' });

                    if (Items.Length < 11)
                        continue;

                    int i1 = Convert.ToInt32(Items[1]);
                    int i2 = Convert.ToInt32(Items[2]);
                    int i3 = Convert.ToInt32(Items[3]);

                    float texCoord1x = Convert.ToSingle(Items[5]); float texCoord1y = Convert.ToSingle(Items[6]);
                    float texCoord2x = Convert.ToSingle(Items[7]); float texCoord2y = Convert.ToSingle(Items[8]);
                    float texCoord3x = Convert.ToSingle(Items[9]); float texCoord3y = Convert.ToSingle(Items[10]);

                    model.AddIndice(i1, i2, i3, new Vector2(texCoord1x, texCoord1y), new Vector2(texCoord2x, texCoord2y), new Vector2(texCoord3x, texCoord3y));
                }
                model.DiffuseTexture = textureName;
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
        public virtual void AddVertex(Vector3 position)
        {
            points[iPoint++] = position;
        }
        public virtual void AddVertex(Vector3 position, Vector3 normal)
        {
            points[iPoint++] = position;
        }
        public virtual void AddIndice(int i1, int i2, int i3)
        {
            // do nothing
        }
        public virtual void AddIndice(int i1, int i2, int i3, Vector2 texCoord1, Vector2 texCoord2, Vector2 texCoord3)
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
            BaseMaterial baseMaterial = null;
            lock (lockThis)
            {
                if (specialRender)
                    baseMaterial = SpecialMaterial;
                else
                    baseMaterial = Material;
                baseMaterial.World = WorldMatrix;
                baseMaterial.Device = graphicsDevice;
                if (baseMaterial is BasicMaterial)
                {
                    ((BasicMaterial)baseMaterial).DiffuseTexture = DiffuseTexture;
                }
                else if (baseMaterial is TextureMaterial)
                {
                    ((TextureMaterial)baseMaterial).DiffuseTexture = DiffuseTexture;
                }
                else if (baseMaterial is FourPointLightsTextureMaterial)
                {
                    ((FourPointLightsTextureMaterial)baseMaterial).DiffuseTexture = DiffuseTexture;
                }
                baseMaterial.Apply();
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
        public VertexTypes Type;
        public long NumPoints;
        public long NumFaces;

        private static bool WriteHeader(FileType fileType, VertexTypes vertexType, long nPoints, long nFaces, string texture, StreamWriter writer)
        {
            bool result = false;
            if (fileType == FileType.PLY && writer != null)
            {
                writer.WriteLine("ply");
                writer.WriteLine("format ascii 1.0");
                if(texture != null && texture.Length > 0)
                    writer.WriteLine("comment TextureFile " + texture);
                writer.WriteLine("element vertex " + nPoints);

                if (vertexType == VertexTypes.XYZ)
                {
                    writer.WriteLine("property float32 x");
                    writer.WriteLine("property float32 y");
                    writer.WriteLine("property float32 z");
                    writer.WriteLine("element face " + nFaces);
                    writer.WriteLine("property list uchar int vertex_indices");
                    writer.WriteLine("end_header");
                }
                else if (vertexType == VertexTypes.XYZ_RGB)
                {
                    writer.WriteLine("property float32 x");
                    writer.WriteLine("property float32 y");
                    writer.WriteLine("property float32 z");
                    writer.WriteLine("property uchar red");
                    writer.WriteLine("property uchar green");
                    writer.WriteLine("property uchar blue");
                    writer.WriteLine("element face " + nFaces);                
                    writer.WriteLine("property list uchar int vertex_indices");
                    writer.WriteLine("end_header");
                }
                else if (vertexType == VertexTypes.XYZ_RGB_NORNAL)
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
                    writer.WriteLine("element face " + nFaces);               
                    writer.WriteLine("property list uchar int vertex_indices");
                    writer.WriteLine("end_header");
                }
                else if (vertexType == VertexTypes.XYZ_TEXCOORD)
                {
                    writer.WriteLine("property float32 x");
                    writer.WriteLine("property float32 y");
                    writer.WriteLine("property float32 z");
                    writer.WriteLine("element face " + nFaces);                
                    writer.WriteLine("property list uchar int vertex_indices");
                    writer.WriteLine("property list uchar float texcoord");
                    writer.WriteLine("end_header");
                }
                else if (vertexType == VertexTypes.XYZ_NORMAL_TEXCOORD)
                {
                    writer.WriteLine("property float32 x");
                    writer.WriteLine("property float32 y");
                    writer.WriteLine("property float32 z");
                    writer.WriteLine("property float32 nx");
                    writer.WriteLine("property float32 ny");
                    writer.WriteLine("property float32 nz");
                    writer.WriteLine("element face " + nFaces);
                    writer.WriteLine("property list uchar int vertex_indices");
                    writer.WriteLine("property list uchar float texcoord");
                    writer.WriteLine("end_header");
                }
                else
                {
                    return false;
                }                
                result = true;
            }
            return result;
        }

        public bool Export(FileType fileType, VertexTypes vertexType, FileInfo file, bool keepOriginalPosition = false)
        {
            bool result = false;
            using (StreamWriter writer = new StreamWriter(file.Open(FileMode.Create, FileAccess.Write)))
            {
                if (result = WriteHeader(fileType, vertexType, NumPoints, NumFaces, DiffuseTexture, writer))
                {
                    result = Export(fileType, vertexType, writer, keepOriginalPosition);
                }
                writer.Close();
            }
            return result;
        }        

        public static bool ExportAll(VertexTypes vertexType, BaseModel[] models, string batchName, FileType fileType, bool keepOriginalPosition = false)
        {
            bool result = true;
            string storeDirectory = Utils.Global.GetRealModelStoreDirectory();
            for (int i = 0; i < models.Length; i++)
            {
                if (fileType == FileType.PLY)
                {
                    FileInfo file = Utils.Global.GetRealFile(batchName + '_' + i.ToString() + ".ply");
                    //FileInfo file = Utils.Global.GetRealFile(storeDirectory + batchName + '/' + models[i].Name + ".ply");
                    if (models[i].Export(fileType, vertexType, file, keepOriginalPosition) == false)
                        result = false;
                }
            }
            return result;
        }

        public static bool ExportUnitedModel(FileType fileType, VertexTypes vertexType, BaseModel[] models, string batchName)
        {            
            string storeDirectory = Utils.Global.GetRealModelStoreDirectory();
            FileInfo file = new FileInfo(batchName); //Utils.Global.GetRealFile(storeDirectory + batchName + ".ply");

            long nPoints = 0;
            long nFaces = 0;
            for (int i = 0; i < models.Length; i++)
            {
                nPoints += models[i].NumPoints;
                nFaces += models[i].NumFaces;
            }

            bool result = true;
            using (StreamWriter writer = new StreamWriter(file.Open(FileMode.Create, FileAccess.Write)))
            {
                if (result = WriteHeader(fileType, VertexTypes.XYZ_RGB, nPoints, nFaces, null, writer))
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
                writer.Close();
            }
            return result;
        }

        protected bool Export(FileType fileType, VertexTypes vertexType, StreamWriter writer, bool keepOriginalPosition = false)
        {
            if (fileType == FileType.PLY)
            {
                if (ExportVertexData(fileType, vertexType, writer, keepOriginalPosition) == false)
                    return false;
                if (ExportIndiceData(fileType, vertexType, writer) == false)
                    return false;
            }
            return true;
        }
        protected abstract bool ExportVertexData(FileType fileType, VertexTypes vertexType, StreamWriter writer, bool keepOriginalPosition = false);
        protected abstract bool ExportIndiceData(FileType fileType, VertexTypes vertexType, StreamWriter writer, long offset = 0);
        protected abstract BaseMaterial GetDefaultMaterial();
        protected abstract BaseMaterial GetDefaultSpecialMaterial();
        public abstract Type[] GetCompatibleMaterialTypes();

        public abstract System.Windows.Media.Imaging.WriteableBitmap toBitmap( int iWidth, int iHeight, Babylon.Toolbox.OrbitCamera cam);
        public virtual System.Windows.Media.Imaging.WriteableBitmap toBitmap()
        {
            Babylon.Toolbox.OrbitCamera cam = new Babylon.Toolbox.OrbitCamera { Alpha = (float)Math.PI / 2 };

            //setmodel target
            cam.Radius = this.BoundingInfo.BoundingSphereWorld.Radius * 4.0f;
            cam.Target = this.BoundingInfo.BoundingSphereWorld.Center;
            cam.Alpha = cam.Alpha; // to raise event => recompute Position to get new ViewMatrix
            
            return toBitmap(400, 400, cam);
        }
    }
}
