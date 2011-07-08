using System.IO;
using System;
using System.Net;

namespace Babylon
{
    public partial class Scene
    {
        //nhminh
        protected enum Mode { Online, Local };
        protected Mode LoadMode = Mode.Online;

        public event EventHandler<LoadEventArgs> LoadProgressionChanged;
        public event EventHandler Loaded;


        void RaiseLoadProgressionChanged(int progress)
        {
            if (LoadProgressionChanged != null)
                LoadProgressionChanged(this, new LoadEventArgs {Progress = progress});
        }

        //nhminh
        public virtual void LoadLocal(Uri sceneUri)
        {
            LoadMode = Mode.Local;
            throw new NotImplementedException();
        }

        public void Load(Uri sceneUri)
        {
            HttpWebRequest webRequest = (HttpWebRequest)WebRequest.Create(sceneUri);
            string sceneName = Path.GetFileNameWithoutExtension(sceneUri.ToString());
            rootStreamUri = new Uri(sceneUri, string.Format("{0}.streams", sceneName));

            webRequest.BeginGetResponse(a =>
            {
                WebResponse response = webRequest.EndGetResponse(a);
                using (Stream stream = response.GetResponseStream())
                {
                    Load(stream);
                }
            }, null);
        }

        public void Load(Stream catalog)
        {
            lock (this)
            {
                Clear();

                BinaryReader reader = new BinaryReader(catalog);

                Version version = new Version(reader.ReadString());
                bool streamMode = reader.ReadBoolean();
                AutoClear = reader.ReadBoolean();
                ClearColor = reader.ReadColor();
                CheckCollisions = reader.ReadBoolean();
                UnitPerMeter = reader.ReadSingle();
                CollisionEpsilon = reader.ReadSingle();
                Gravity = reader.ReadVector3();
                AmbientColor = reader.ReadColor();

                ItemsToStream = 0;

                // Cameras
                int camerasCount = reader.ReadInt32();
                for (int index = 0; index < camerasCount; index++)
                {
                    Camera camera = new Camera(reader.ReadString(), this);

                    camera.Load(reader);
                    RaiseLoadProgressionChanged(((index * 100) / camerasCount) / 4);
                }

                // Lights
                int lightsCount = reader.ReadInt32();
                for (int index = 0; index < lightsCount; index++)
                {
                    Light light = new Light(reader.ReadString(), this);

                    light.Load(reader);
                    RaiseLoadProgressionChanged(25 + ((index * 100) / lightsCount) / 4);
                }

                // Materials
                int materialsCount = reader.ReadInt32();
                for (int index = 0; index < materialsCount; index++)
                {
                    string materialType = reader.ReadString();

                    if (materialType == "NOP")
                        continue;

                    switch (materialType)
                    {
                        case "STD":
                            StandardMaterial standardMaterial = new StandardMaterial(reader.ReadString(), this);
                            standardMaterial.Load(reader, streamMode);
                            break;
                        case "PPS":
                            PerPixelMaterial perPixelMaterial = new PerPixelMaterial(reader.ReadString(), this);
                            perPixelMaterial.Load(reader, streamMode);
                            break;
                        case "MM":
                            MultiMaterial multiMaterial = new MultiMaterial(reader.ReadString(), this);
                            multiMaterial.Load(reader);
                            break;
                    }

                    RaiseLoadProgressionChanged(50 + ((index * 100) / materialsCount) / 4);
                }

                // Models
                int modelsCount = reader.ReadInt32();
                for (int index = 0; index < modelsCount; index++)
                {
                    Model model = new Model(reader.ReadString(), this);

                    model.Load(reader, streamMode);
                    RaiseLoadProgressionChanged(75 + ((index * 100) / modelsCount) / 4);
                }

                // Targets && Parents
                foreach (Camera camera in cameras)
                {
                    if (camera.LoadedTargetID.HasValue)
                    {
                        camera.Target = FindEntity(camera.LoadedTargetID.Value);
                        camera.LoadedTargetID = null;
                    }

                    if (camera.LoadedParentID.HasValue)
                    {
                        camera.ParentEntity = FindEntity(camera.LoadedParentID.Value);
                        camera.LoadedParentID = null;
                    }
                }

                foreach (Model model in models)
                {
                    if (model.LoadedTargetID.HasValue)
                    {
                        model.Target = FindEntity(model.LoadedTargetID.Value);
                        model.LoadedTargetID = null;
                    }
                    if (model.LoadedParentID.HasValue)
                    {
                        model.ParentEntity = FindEntity(model.LoadedParentID.Value);
                        model.LoadedParentID = null;
                    }
                }

                foreach (Light light in lights)
                {
                    if (light.LoadedParentID.HasValue)
                    {
                        light.ParentEntity = FindEntity(light.LoadedParentID.Value);
                        light.LoadedParentID = null;
                    }
                }

                reader.Dispose();

                if (Loaded != null)
                    Loaded(this, EventArgs.Empty);
            }
        }
    }
}
