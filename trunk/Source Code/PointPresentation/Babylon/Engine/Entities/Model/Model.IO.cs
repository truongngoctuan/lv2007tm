using System.IO;
using Babylon.Toolbox;
using Microsoft.Xna.Framework;

namespace Babylon
{
    public partial class Model
    {
        int verticesToStream;
        int facesToStream;
        bool has2TexturesCoordinatesSystem;
        bool is32Bits;

        public int StreamID { get; private set; }

        internal void Load(BinaryReader reader, bool streamMode)
        {
            ID = reader.ReadGuid();
            material = Scene.FindMaterial(reader.ReadGuid());
            LoadedParentID = reader.ReadGuid();

            Enabled = reader.ReadBoolean();
            Renderable = reader.ReadBoolean();
            Billboard = reader.ReadBoolean();
            BillboardX = reader.ReadBoolean();
            BillboardY = reader.ReadBoolean();
            BillboardZ = reader.ReadBoolean();
            CheckCollisions = reader.ReadBoolean();

            if (!CheckCollisions && streamMode)
            {
                Scene.ItemsToStream++;
                StreamingState = StreamingState.PreLoaded;
            }
            else
                StreamingState = StreamingState.Loaded;

            // World
            PositionRelativeToParent = reader.ReadVector3();
            Rotation = reader.ReadVector3();
            Scaling = reader.ReadVector3();
            localMatrix = reader.ReadMatrix();

            // Vertices
            verticesToStream = reader.ReadInt32();
            has2TexturesCoordinatesSystem = reader.ReadBoolean();

            if (StreamingState == StreamingState.PreLoaded)
            {
                StreamID = reader.ReadInt32();
            }
            else
                LoadVertices(reader);

            // Faces
            facesToStream = reader.ReadInt32();
            is32Bits = reader.ReadBoolean();

            if (StreamingState != StreamingState.PreLoaded)
                LoadFaces(reader);

            // SubModels
            subModels.Clear();

            int subobjects = reader.ReadInt32();
            for (int index = 0; index < subobjects; index++)
            {
                int attributeID = reader.ReadInt32();
                int faceStart = reader.ReadInt32();
                int faceCount = reader.ReadInt32();
                int vertexStart = reader.ReadInt32();
                int vertexCount = reader.ReadInt32();

                SubModel subModel = new SubModel(this, attributeID, vertexStart, faceStart * 3, faceCount, vertexCount);

                if (StreamingState == StreamingState.Loaded)
                    subModel.PrepareSubModel();

                subModels.Add(subModel);
            }
        }

        void LoadVertices(BinaryReader reader)
        {
            Vector3[] points = new Vector3[verticesToStream];

            if (!has2TexturesCoordinatesSystem)
            {
                VertexPositionNormalTexture[] vertices = new VertexPositionNormalTexture[verticesToStream];

                for (int index = 0; index < verticesToStream; index++)
                {
                    Vector3 pos = reader.ReadVector3();
                    vertices[index].Position = pos;
                    points[index] = pos;

                    vertices[index].Normal = reader.ReadVector3();
                    vertices[index].TextureCoordinates = reader.ReadVector2();
                }
                // for BabylonToolkit v1.0.0
                // vertices[0].Stride always return 32
                //SetVertexBufferData(vertices, vertices[0].VertexDeclaration, vertices[0].Stride, points);

                // for BabylonToolkit v1.0.4
                SetVertexBufferData(vertices, vertices[0].VertexDeclaration, 32, points);
            }
            else // Beurk..Must find a solution to factorize code here!
            {
                VertexPositionNormalTexture2[] vertices = new VertexPositionNormalTexture2[verticesToStream];

                for (int index = 0; index < verticesToStream; index++)
                {
                    Vector3 pos = reader.ReadVector3();
                    vertices[index].Position = pos;
                    points[index] = pos;

                    vertices[index].Normal = reader.ReadVector3();
                    vertices[index].TextureCoordinate01 = reader.ReadVector2();
                    vertices[index].TextureCoordinate02 = reader.ReadVector2();
                }

                SetVertexBufferData(vertices, VertexPositionNormalTexture2.VertexDeclaration, VertexPositionNormalTexture2.Stride, points);
            }
        }

        private void LoadFaces(BinaryReader reader)
        {
            if (is32Bits)
            {
                int[] indices = new int[facesToStream * 3];
                for (int index = 0; index < facesToStream * 3; index++)
                {
                    indices[index] = reader.ReadInt32();
                }

                SetIndexBufferData(indices);
            }
            else
            {
                ushort[] indices = new ushort[facesToStream * 3];
                for (int index = 0; index < facesToStream * 3; index++)
                {
                    indices[index] = reader.ReadUInt16();
                }

                SetIndexBufferData(indices);
            }
        }

        public void ProcessStream(Stream stream)
        {
            using (BinaryReader reader = new BinaryReader(stream))
            {
                LoadVertices(reader);
                LoadFaces(reader);

                foreach (SubModel subModel in subModels)
                {
                    subModel.PrepareSubModel();
                }
            }

            StreamingState = StreamingState.Loaded;
        }
    }
}
