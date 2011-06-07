

using Microsoft.Xna.Framework;
using _3DPresentation.Models;
using Microsoft.Xna.Framework.Graphics;
namespace _3DPresentation
{
    public class LightPoint
    {
        private Vector3 _position;
        public Vector3 Position
        {
            get
            {
                return _position;
            }
            set
            {
                _position = value;
                if(Model != null)
                    Model.WorldMatrix = Matrix.CreateTranslation(Position);
            }
        }        
        public Color LightColor { get; set; }
        public float Intensity { get; set; }
        public SimpleModel Model { get; set; }

        public SimpleModel GetDefaultModel(GraphicsDevice graphicsDevice)
        {
            VertexPositionColor[] lightSourceVertices = new VertexPositionColor[36];
            // face coordinates
            Vector3 topLeftFront = new Vector3(-10.0f, 10.0f, 10.0f);
            Vector3 bottomLeftFront = new Vector3(-10.0f, -10.0f, 10.0f);
            Vector3 topRightFront = new Vector3(10.0f, 10.0f, 10.0f);
            Vector3 bottomRightFront = new Vector3(10.0f, -10.0f, 10.0f);
            Vector3 topLeftBack = new Vector3(-10.0f, 10.0f, -10.0f);
            Vector3 topRightBack = new Vector3(10.0f, 10.0f, -10.0f);
            Vector3 bottomLeftBack = new Vector3(-10.0f, -10.0f, -10.0f);
            Vector3 bottomRightBack = new Vector3(10.0f, -10.0f, -10.0f);

            // front face
            lightSourceVertices[0] = new VertexPositionColor(topRightFront, GlobalVars.Red);
            lightSourceVertices[1] = new VertexPositionColor(bottomLeftFront, GlobalVars.Orange);
            lightSourceVertices[2] = new VertexPositionColor(topLeftFront, GlobalVars.Yellow);
            lightSourceVertices[3] = new VertexPositionColor(topRightFront, GlobalVars.Red);
            lightSourceVertices[4] = new VertexPositionColor(bottomRightFront, GlobalVars.Green);
            lightSourceVertices[5] = new VertexPositionColor(bottomLeftFront, GlobalVars.Orange);

            // back face 
            lightSourceVertices[6] = new VertexPositionColor(bottomLeftBack, GlobalVars.Blue);
            lightSourceVertices[7] = new VertexPositionColor(topRightBack, GlobalVars.Purple);
            lightSourceVertices[8] = new VertexPositionColor(topLeftBack, GlobalVars.Black);
            lightSourceVertices[9] = new VertexPositionColor(bottomRightBack, GlobalVars.Cyan);
            lightSourceVertices[10] = new VertexPositionColor(topRightBack, GlobalVars.Purple);
            lightSourceVertices[11] = new VertexPositionColor(bottomLeftBack, GlobalVars.Blue);

            // top face
            lightSourceVertices[12] = new VertexPositionColor(topLeftBack, GlobalVars.Black);
            lightSourceVertices[13] = new VertexPositionColor(topRightBack, GlobalVars.Purple);
            lightSourceVertices[14] = new VertexPositionColor(topLeftFront, GlobalVars.Yellow);
            lightSourceVertices[15] = new VertexPositionColor(topRightBack, GlobalVars.Purple);
            lightSourceVertices[16] = new VertexPositionColor(topRightFront, GlobalVars.Red);
            lightSourceVertices[17] = new VertexPositionColor(topLeftFront, GlobalVars.Yellow);

            // bottom face 
            lightSourceVertices[18] = new VertexPositionColor(bottomRightBack, GlobalVars.Cyan);
            lightSourceVertices[19] = new VertexPositionColor(bottomLeftBack, GlobalVars.Blue);
            lightSourceVertices[20] = new VertexPositionColor(bottomLeftFront, GlobalVars.Orange);
            lightSourceVertices[21] = new VertexPositionColor(bottomRightFront, GlobalVars.Green);
            lightSourceVertices[22] = new VertexPositionColor(bottomRightBack, GlobalVars.Cyan);
            lightSourceVertices[23] = new VertexPositionColor(bottomLeftFront, GlobalVars.Orange);

            // left face
            lightSourceVertices[24] = new VertexPositionColor(bottomLeftFront, GlobalVars.Orange);
            lightSourceVertices[25] = new VertexPositionColor(bottomLeftBack, GlobalVars.Blue);
            lightSourceVertices[26] = new VertexPositionColor(topLeftFront, GlobalVars.Yellow);
            lightSourceVertices[27] = new VertexPositionColor(topLeftFront, GlobalVars.Yellow);
            lightSourceVertices[28] = new VertexPositionColor(bottomLeftBack, GlobalVars.Blue);
            lightSourceVertices[29] = new VertexPositionColor(topLeftBack, GlobalVars.Black);

            // right face 
            lightSourceVertices[30] = new VertexPositionColor(bottomRightBack, GlobalVars.Cyan);
            lightSourceVertices[31] = new VertexPositionColor(bottomRightFront, GlobalVars.Green);
            lightSourceVertices[32] = new VertexPositionColor(topRightFront, GlobalVars.Red);
            lightSourceVertices[33] = new VertexPositionColor(bottomRightBack, GlobalVars.Cyan);
            lightSourceVertices[34] = new VertexPositionColor(topRightFront, GlobalVars.Red);
            lightSourceVertices[35] = new VertexPositionColor(topRightBack, GlobalVars.Purple);

            SimpleModel simpleModel = SimpleModel.CreateModel(graphicsDevice, lightSourceVertices);
            simpleModel.RenderType = SimpleModel.Type.TriangleList;
            simpleModel.WorldMatrix = Matrix.CreateTranslation(Position);
            return simpleModel;
        }
        public LightPoint(Vector3 position, Color color, float intensity)
        {
            Position = position;
            LightColor = color;
            Intensity = intensity;
        }
    }
}
