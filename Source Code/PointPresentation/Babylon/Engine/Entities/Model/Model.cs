using System;
using System.Collections.Generic;
using Microsoft.Xna.Framework;
using Microsoft.Xna.Framework.Graphics;

namespace Babylon
{
    public partial class Model : Entity, IStreamableData
    {
        Material material;
        Matrix localMatrix;
        readonly List<SubModel> subModels = new List<SubModel>();

        public Vector3 Scaling { get; set; }

        public Material Material
        {
            get
            {
                if (material == null)
                    return Scene.DefaultMaterial;
                return material;
            }
            set
            {
                material = value;
            }
        }

        public VertexBuffer VertexBuffer { get; private set; }
        public IndexBuffer IndexBuffer { get; private set; }
        public int FacesCount { get; private set; }
        public int VerticesCount { get; private set; }

        public float Visibility { get; set; }

        public bool Renderable { get; set; }

        public BoundingInfo BoundingInfo { get; private set; }

        public bool Use2TexturesCoordinates { get; set; }

        public Vector3[] Points { get; private set; }

        public bool Billboard { get; set; }

        public bool BillboardX { get; set; }

        public bool BillboardY { get; set; }

        public bool BillboardZ { get; set; }

        public float Determinant { get; set; }

        public int[] Indices { get; private set; }

        public List<SubModel> SubModels
        {
            get { return subModels; }
        }

        public StreamingState StreamingState { get; set; }
        
        internal override float ScaleFactor
        {
            get
            {
                float scaleFactor = Math.Max(Scaling.X, Scaling.Y);
                scaleFactor = Math.Max(scaleFactor, Scaling.Z);

                if (ParentEntity != null)
                    return scaleFactor * ParentEntity.ScaleFactor;
                return scaleFactor;
            }
        }

        public override void ComputeMatrices()
        {
            if (MustRecomputeMatrices())
            {
                Matrix matTranslation = MatrixLeftHanded.CreateTranslation(PositionRelativeToParent);

                if (Target != null)
                {
                    if (Target is Entity)
                        (Target as Entity).ComputeMatrices();

                    ComputeRotationByTarget(Target.Position, false);
                }

                // World
                world = Matrix.CreateScale(Scaling) * localMatrix * MatrixLeftHanded.CreateScale(Determinant, Determinant, Determinant) * MatrixLeftHanded.CreateFromYawPitchRoll(Rotation.Y, Rotation.X, Rotation.Z);

                // BillBoard
                if (Billboard)
                {
                    Vector3 localPosition = PositionRelativeToParent;
                    Vector3 zero = Scene.ActiveCamera.Position;

                    if (ParentEntity != null)
                    {
                        localPosition += ParentEntity.Position;
                        matTranslation = MatrixLeftHanded.CreateTranslation(localPosition);
                    }

                    if (BillboardX)
                        zero.X = localPosition.X + 0.0001f;
                    if (BillboardY)
                        zero.Y = localPosition.Y + 0.0001f;
                    if (BillboardZ)
                        zero.Z = localPosition.Z + 0.0001f;

                    if (BillboardX && BillboardY && BillboardZ)
                        zero = Scene.ActiveCamera.Position;

                    Matrix matBillboard = MatrixLeftHanded.CreateLookAt(localPosition, zero, Vector3.Up);
                    matBillboard.M41 = matBillboard.M42 = matBillboard.M43 = 0;

                    world *= MatrixLeftHanded.Invert(matBillboard);
                }

                // Translation
                world *= matTranslation;

                // Parent
                if (ParentEntity != null && !Billboard)
                {
                    Matrix parentWorld = Matrix.Identity;

                    if (Target != null)
                    {
                        parentWorld.M41 = ParentMatrix.M41;
                        parentWorld.M42 = ParentMatrix.M42;
                        parentWorld.M43 = ParentMatrix.M43;
                    }
                    else
                    {
                        if (InheritType == InheritTypes.All)
                            parentWorld = ParentMatrix;
                        else
                        {
                            parentWorld.M41 = ParentMatrix.M41;
                            parentWorld.M42 = ParentMatrix.M42;
                            parentWorld.M43 = ParentMatrix.M43;
                        }
                    }

                    world = world * parentWorld;
                }

                Position = new Vector3(world.M41, world.M42, world.M43);

                if (BoundingInfo == null)
                    return;
                BoundingInfo.UpdateWorldDatas(world, ScaleFactor);

                foreach (SubModel subObject in subModels)
                {
                    subObject.BoundingInfo.UpdateWorldDatas(world, ScaleFactor);
                }
            }
        }

        internal Model(string name, Scene scene)
            : base(name, scene)
        {
            Renderable = true;
            Visibility = 1f;
            scene.Models.Add(this);

            Determinant = 1.0f;
            Scaling = new Vector3(1, 1, 1);
            localMatrix = Matrix.Identity;
        }

        public override void Dispose()
        {
            VertexBuffer = null;
            IndexBuffer = null;
        }

        public void SetVertexBufferData<T>(T[] datas, VertexDeclaration vertexDeclaration, int stride, Vector3[] pointsArray) where T : struct
        {
            VertexBuffer = new VertexBuffer(Engine.Device, vertexDeclaration, datas.Length, BufferUsage.WriteOnly);

            VertexBuffer.SetData(0, datas, 0, datas.Length, stride);

            Points = pointsArray;

            BoundingInfo = new BoundingInfo(pointsArray);

            VerticesCount = datas.Length;
        }

        public void SetIndexBufferData(ushort[] datas)
        {
            IndexBuffer = new IndexBuffer(Engine.Device, IndexElementSize.SixteenBits, datas.Length, BufferUsage.WriteOnly);

            IndexBuffer.SetData(0, datas, 0, datas.Length);

            FacesCount = (datas.Length / 3);

            Indices = new int[datas.Length];
            for (int index = 0; index < datas.Length; index++)
            {
                Indices[index] = datas[index];
            }
        }

        public void SetIndexBufferData(int[] datas)
        {
            IndexBuffer = new IndexBuffer(Engine.Device, IndexElementSize.ThirtyTwoBits, datas.Length, BufferUsage.WriteOnly);

            IndexBuffer.SetData(0, datas, 0, datas.Length);

            FacesCount = datas.Length / 3;

            Indices = datas;
        }
    }
}
