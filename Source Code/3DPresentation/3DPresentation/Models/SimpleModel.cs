using Microsoft.Xna.Framework.Graphics;
using Microsoft.Xna.Framework;


namespace _3DPresentation.Models
{
    public class SimpleModel
    {
        public enum Type { LineList, LineStrip, TriangleList, TriangleStrip }
        VertexBuffer vertexBuffer;

        public Type RenderType { get; set; }
        public Matrix WorldMatrix { get; set; }
        private SimpleModel()
        {
        }

        public static SimpleModel CreateModel(GraphicsDevice graphicsDevice, VertexPositionColor[] vertices)
        {
            SimpleModel simpleModel = new SimpleModel();
            simpleModel.vertexBuffer = new VertexBuffer(graphicsDevice, VertexPositionColor.VertexDeclaration,
                vertices.Length, BufferUsage.WriteOnly);
            simpleModel.vertexBuffer.SetData(0, vertices, 0, vertices.Length, 0);

            simpleModel.WorldMatrix = Matrix.Identity;
            return simpleModel;
        }

        public void Render(GraphicsDevice graphicsDevice)
        {
            graphicsDevice.SetVertexBuffer(vertexBuffer);
            switch (RenderType)
            {
                case Type.LineList:
                {
                    graphicsDevice.DrawPrimitives(PrimitiveType.LineList, 0, vertexBuffer.VertexCount / 2);
                    break;
                }
                case Type.LineStrip:
                {
                    graphicsDevice.DrawPrimitives(PrimitiveType.LineStrip, 0, vertexBuffer.VertexCount - 1);
                    break;
                }
                case Type.TriangleList:
                {
                    graphicsDevice.DrawPrimitives(PrimitiveType.TriangleList, 0, vertexBuffer.VertexCount / 3);
                    break;
                }
                case Type.TriangleStrip:
                {
                    graphicsDevice.DrawPrimitives(PrimitiveType.TriangleStrip, 0, vertexBuffer.VertexCount - 2);
                    break;
                }
            }            
        }
    }
}
