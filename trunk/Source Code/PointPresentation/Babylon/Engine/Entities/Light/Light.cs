using Babylon.Maths;
using Microsoft.Xna.Framework;

namespace Babylon
{
    public partial class Light : Entity
    {
        public Vector3 DirectionRelativeToParent { get; set; }

        public Color Diffuse { get; set; }

        public Color Specular { get; set; }

        public Vector3 Direction { get; set; }

        public LightType Type { get; set; }

        public Light(string name, Scene scene)
            : base(name, scene)
        {
            scene.Lights.Add(this);
            Diffuse = Color.White;
            Specular = Color.White;
            Type = LightType.Point;
        }
        
        public override void Dispose()
        {
        }

        public override void ComputeMatrices()
        {
            if (ParentEntity != null)
            {
                Matrix parentWorld = Matrix.Identity;

                if (InheritType == InheritTypes.All)
                    parentWorld = ParentMatrix;
                else
                {
                    parentWorld.M41 = ParentMatrix.M41;
                    parentWorld.M42 = ParentMatrix.M42;
                    parentWorld.M43 = ParentMatrix.M43;
                }

                Position = Vector3.Transform(PositionRelativeToParent, parentWorld);
                Direction = Vector3.TransformNormal(DirectionRelativeToParent, parentWorld);
            }
            else
            {
                Position = PositionRelativeToParent;
                Direction = DirectionRelativeToParent;
            }
        }
    }
}
