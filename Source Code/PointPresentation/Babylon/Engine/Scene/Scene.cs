using Microsoft.Xna.Framework;

namespace Babylon
{
    public partial class Scene : RootElement
    {
        readonly Engine engine;
        readonly StandardMaterial defaultMaterial;
        readonly InputManager controlManager;

        public Color AmbientColor { get; set; }

        public Material DefaultMaterial
        {
            get
            {
                return defaultMaterial;
            }
        }

        public Camera ActiveCamera { get; set; }

        public Engine Engine
        {
            get { return engine; }
        }

        public Color ClearColor { get; set; }
        public bool AutoClear { get; set; }
        public bool ForceWireframe { get; set; }

        public InputManager ControlManager
        {
            get { return controlManager; }
        }

        public Scene(string name, Engine engine) : base(name)
        {
            UnitPerMeter = 0.01f;
            CollisionEpsilon = 0.0005f;
            AutoClear = true;
            ClearColor = Color.White;
            AmbientColor = Color.Black;
            this.engine = engine;
            engine.Scenes.Add(this);

            defaultMaterial = new StandardMaterial("defaultMaterial", this);

            cameras.CollectionChanged += cameras_CollectionChanged;

            controlManager = new InputManager(this);
        }

        public override void Dispose()
        {
            cameras.CollectionChanged -= cameras_CollectionChanged;

            Engine.Scenes.Remove(this);

            Clear();
        }

        public void Clear()
        {
            foreach (Model model in models)
            {
                model.Dispose();
            }
            models.Clear();

            foreach (Camera camera in cameras)
            {
                camera.Dispose();
            }
            cameras.Clear();

            foreach (Light light in lights)
            {
                light.Dispose();
            }
            lights.Clear();

            foreach (Material material in materials)
            {
                material.Dispose();
            }
            materials.Clear();
        }
    }
}
