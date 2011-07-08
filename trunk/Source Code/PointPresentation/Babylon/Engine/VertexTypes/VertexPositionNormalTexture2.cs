using Microsoft.Xna.Framework;
using Microsoft.Xna.Framework.Graphics;

namespace Babylon
{
    public struct VertexPositionNormalTexture2
    {
        static readonly VertexDeclaration vertexDeclaration = new VertexDeclaration(
                    new VertexElement(0, VertexElementFormat.Vector3, VertexElementUsage.Position, 0),
                    new VertexElement(12, VertexElementFormat.Vector3, VertexElementUsage.Normal, 0),
                    new VertexElement(24, VertexElementFormat.Vector2, VertexElementUsage.TextureCoordinate, 0),
                    new VertexElement(32, VertexElementFormat.Vector2, VertexElementUsage.TextureCoordinate, 1)
                    );

        public const int Stride = 40;

        public Vector3 Position;
        public Vector3 Normal;
        public Vector2 TextureCoordinate01;
        public Vector2 TextureCoordinate02;

        public static VertexDeclaration VertexDeclaration
        {
            get { return vertexDeclaration; }
        }
    }
}

