using System;
using System.Collections.Generic;
using System.Diagnostics;
using Microsoft.Xna.Framework;

namespace Babylon
{
    [DebuggerDisplay("Name = {Name}")]
    public abstract partial class Entity : Targetable
    {
        Entity parentEntity;
        readonly List<Entity> children = new List<Entity>();
        long currentRenderID = -1;
        protected Matrix world = Matrix.Identity;
        InheritTypes inheritType = InheritTypes.All;

        internal Guid? LoadedTargetID { get; set; }
        internal Guid? LoadedParentID { get; set; }

        Vector3 positionRelativeToParent;
        protected Vector3 PositionRelativeToParent
        {
            get { return positionRelativeToParent; }
            set
            {
                positionRelativeToParent = value;
                ComputeMatrices();
            }
        }

        public Vector3 Rotation { get; set; }
        public float RotationX
        {
            get { return Rotation.X; }
            set { Rotation = new Vector3(value, Rotation.Y, Rotation.Z); }
        }

        public float RotationY
        {
            get { return Rotation.Y; }
            set { Rotation = new Vector3(Rotation.X, value, Rotation.Z); }
        }

        public float RotationZ
        {
            get { return Rotation.Z; }
            set { Rotation = new Vector3(Rotation.X, Rotation.Y, value); }
        }

        public bool Enabled { get; set; }

        public Scene Scene { get; private set; }

        public override Vector3 Position
        {
            get
            {
                return base.Position;
            }
            set
            {
                if (parentEntity == null)
                    positionRelativeToParent = value;
                else
                {
                    if (InheritType == InheritTypes.OnlyPosition)
                        positionRelativeToParent = value - parentEntity.PositionRelativeToParent;
                    else
                        positionRelativeToParent = Vector3.Transform(value, Matrix.Invert(ParentMatrix));
                }

                base.Position = value;
            }
        }

        public Targetable Target { get; set; }

        public Entity ParentEntity
        {
            get { return parentEntity; }
            set
            {
                if (value == parentEntity)
                    return;

                if (value == null && parentEntity != null)
                    parentEntity.children.Remove(this);

                parentEntity = value;

                if (value != null)
                    value.children.Add(this);
            }
        }

        internal virtual float ScaleFactor
        {
            get
            {
                return 1.0f;
            }
        }

        public virtual Matrix World
        {
            get
            {
                return world;
            }
        }

        public Matrix ParentMatrix
        {
            get
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

                return matrix;
            }
        }

        public InheritTypes InheritType
        {
            get
            {
                return inheritType;
            }

            set
            {
                inheritType = value;
            }
        }

        public Engine Engine { get; private set; }

        internal Entity(string name, Scene scene)
            : base(name)
        {
            Enabled = true;
            Scene = scene;
            Engine = scene.Engine;
        }

        protected bool MustRecomputeMatrices()
        {
            if (Scene.RenderID != currentRenderID)
            {
                currentRenderID = Scene.RenderID;
                return true;
            }
            return false;
        }

        public abstract void ComputeMatrices();

        /// <summary>
        /// Compute rotation vector using target position.
        /// </summary>
        /// <param name="targetPosition">Target position in world space.</param>
        /// <param name="onlyYRotation">Compute only rotation for Y axis.</param>
        public void ComputeRotationByTarget(Vector3 targetPosition, bool onlyYRotation)
        {
            Matrix camMatrix = MatrixLeftHanded.Invert(MatrixLeftHanded.CreateLookAt(Position, targetPosition, new Vector3(0, 1f, 0)));

            if (!onlyYRotation)
                RotationX = (float)Math.Atan(camMatrix.M23 / camMatrix.M33);

            Vector3 vDir = targetPosition - Position;

            if (vDir.X >= 0.0f)
                RotationY = (float)(-Math.Atan(vDir.Z / vDir.X) + Math.PI / 2.0);
            else
                RotationY = (float)(-Math.Atan(vDir.Z / vDir.X) - Math.PI / 2.0);

            RotationZ = 0;

            if (float.IsNaN(Rotation.X))
                RotationX = 0;

            if (float.IsNaN(Rotation.Y))
                RotationY = 0;

            if (float.IsNaN(Rotation.Z))
                RotationZ = 0;
        }
    }
}
