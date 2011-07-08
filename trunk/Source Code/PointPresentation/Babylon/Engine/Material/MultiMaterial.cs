using System;
using System.Collections.ObjectModel;
using System.IO;

namespace Babylon
{
    public class MultiMaterial : Material
    {
        readonly ObservableCollection<Material> materials = new ObservableCollection<Material>();
        public MultiMaterial(string name, Scene scene)
            : base(name, scene)
        {
        }

        public ObservableCollection<Material> Materials
        {
            get { return materials; }
        }

        internal override Material GetEffectiveMaterial(int materialID)
        {
            if (materialID >= materials.Count)
                return materials[0];

            return materials[materialID];
        }

        public override void Render(SubModel subModel)
        {
        }

        public override void Dispose()
        {
            foreach (Material material in materials)
            {
                if (material != null)
                    material.Dispose();
            }

            base.Dispose();
        }

        internal void Load(BinaryReader reader)
        {
            ID = reader.ReadGuid();
            int subMaterialsCount = reader.ReadInt32();

            for (int index = 0; index < subMaterialsCount; index++)
            {
                Guid id = reader.ReadGuid();

                materials.Add(Scene.FindMaterial(id));
            }
        }
    }
}
