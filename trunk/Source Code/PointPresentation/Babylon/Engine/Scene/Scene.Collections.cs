using System;
using System.Collections.ObjectModel;
using System.Collections.Specialized;
using System.Linq;

namespace Babylon
{
    public partial class Scene
    {
        readonly ObservableCollection<Camera> cameras = new ObservableCollection<Camera>();
        readonly ObservableCollection<Model> models = new ObservableCollection<Model>();
        readonly ObservableCollection<Light> lights = new ObservableCollection<Light>();
        readonly ObservableCollection<Material> materials = new ObservableCollection<Material>();

        public ObservableCollection<Camera> Cameras
        {
            get { return cameras; }
        }

        public ObservableCollection<Model> Models
        {
            get { return models; }
        }

        public ObservableCollection<Material> Materials
        {
            get { return materials; }
        }

        public ObservableCollection<Light> Lights
        {
            get { return lights; }
        }

        void cameras_CollectionChanged(object sender, NotifyCollectionChangedEventArgs e)
        {
            if (cameras.Count == 1)
            {
                ActiveCamera = cameras[0];
                return;
            }

            if (cameras.Count == 0)
            {
                ActiveCamera = null;
                return;
            }

            if (e.OldItems != null && e.OldItems.Contains(ActiveCamera))
            {
                ActiveCamera = cameras.Last();
            }
        }

        public Entity FindEntity(Guid id)
        {
            if (id == Guid.Empty)
                return null;

            Entity result = cameras.Where(c => c.ID == id).FirstOrDefault();

            if (result != null)
                return result;

            result = models.Where(m => m.ID == id).FirstOrDefault();

            if (result != null)
                return result;

            result = lights.Where(l => l.ID == id).FirstOrDefault();

            if (result != null)
                return result;

            return null;
        }

        public Material FindMaterial(Guid id)
        {
            return Materials.Where(m => m.ID == id).FirstOrDefault();
        }
    }
}
