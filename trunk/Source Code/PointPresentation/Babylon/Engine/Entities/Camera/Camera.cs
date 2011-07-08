using Babylon.Maths;
using Microsoft.Xna.Framework;

namespace Babylon
{
    public partial class Camera
    {
        Matrix view;
        Matrix projection;

        public float NearClip { get; set; }

        public float FarClip { get; set; }

        public float Inertia { get; set; }

        public Matrix View
        {
            get
            {
                ComputeMatrices();
                return view;
            }
        }

        public Matrix Projection
        {
            get
            {
                ComputeMatrices();
                return projection;
            }
        }

        public float NearPlane { get; set; }

        public float FarPlane { get; set; }

        public float Speed { get; set; }

        public float SpeedFactor { get; set; }

        public float FOV { get; set; }

        public bool IsFlying { get; set; }

        public Camera(string name, Scene scene) : base(name, scene)
        {
            FOV = MathHelper.PiOver4;
            SpeedFactor = 3.0f;
            Speed = 1.0f;
            FarPlane = 1000.0f;
            FarClip = 1000.0f;
            NearClip = 0.1f;
            CollisionsEpsilon = 0.001f;

            scene.Cameras.Add(this);
        }

        public override void Dispose()
        {
            
        }

        public override void ComputeMatrices()
        {
            if (MustRecomputeMatrices())
            {
                if (ParentEntity != null)
                {
                    Matrix matrix = Matrix.Identity;

                    switch (InheritType)
                    {
                        case InheritTypes.All:
                            matrix = ParentEntity.World;
                            break;
                        case InheritTypes.OnlyPosition:
                            matrix.M41 = ParentEntity.World.M41;
                            matrix.M42 = ParentEntity.World.M42;
                            matrix.M43 = ParentEntity.World.M43;
                            break;
                    }

                    Position = Vector3.Transform(PositionRelativeToParent, matrix);
                }
                else
                    Position = PositionRelativeToParent;

                if (Target != null)
                    view = MatrixLeftHanded.CreateLookAt(Position, Target.Position, Vector3.Up);
                else
                {
                    Vector3 referencePoint = new Vector3(0, 0, 1f);
                    Matrix transform = MatrixLeftHanded.CreateFromYawPitchRoll(Rotation.Y, Rotation.X, Rotation.Z);

                    Vector3 newTarget = Position + Vector3.Transform(referencePoint, transform);

                    view = MatrixLeftHanded.CreateLookAt(Position, newTarget, Vector3.Up);
                }

                world = MatrixLeftHanded.Invert(view);

                projection = MatrixLeftHanded.CreatePerspectiveFieldOfView(FOV, Scene.Engine.AspectRatio, NearClip, FarClip);
                ComputeFrustumPlanes();
            }
        }
    }
}
