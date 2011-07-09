using System;
using System.Collections.Generic;
using System.IO;
using Microsoft.Xna.Framework;
using Microsoft.Xna.Framework.Graphics;

namespace _3DPresentation.Models
{
    public class FaceModel : BaseModel
    {
        // component
        FaceManager faceManager;
             
        public FaceModel()
        {
            faceManager = new FaceManager();
        }

        public override void Begin(int nPoints, int nFaces)
        {
            base.Begin(nPoints, nFaces);
            faceManager.Begin(nPoints, nFaces);
        }
        public override void AddVertex(Vector3 position, Color color)
        {
            base.AddVertex(position, color);
            faceManager.AddVertex(position, color);
        }
        public override void AddIndice(int i1, int i2, int i3)
        {
            base.AddIndice(i1, i2, i3);
            faceManager.AddIndice(i1, i2, i3);
        }
        public override void End()
        {
            base.End();
            faceManager.End();
        }

        public override void InitBuffers(GraphicsDevice graphicsDevice)
        {
            faceManager.InitBuffers(graphicsDevice);
        }

        public override void Render(GraphicsDevice graphicsDevice)
        {
            base.Render(graphicsDevice);
            if (IsInitialized == false)
                return;

            faceManager.Render(graphicsDevice);
        }
             
    }
}
