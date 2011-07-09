using System;
using System.Collections.Generic;
using System.IO;
using Microsoft.Xna.Framework;
using Microsoft.Xna.Framework.Graphics;

namespace _3DPresentation.Models
{
    public class PointModel : BaseModel
    {
        PointManager pointManager;
        public PointModel()
        {
            pointManager = new PointManager();
        }

        public override void Begin(int nPoints, int nFaces)
        {
            base.Begin(nPoints, nFaces);
            pointManager.Begin(nPoints);
        }
        public override void AddVertex(Vector3 position, Color color)
        {
            base.AddVertex(position, color);
            pointManager.AddVertex(position, color);
        }
        public override void AddIndice(int i1, int i2, int i3)
        {
            base.AddIndice(i1, i2, i3);
        }
        public override void End()
        {
            base.End();
            pointManager.End();
        }
        
        public override void InitBuffers(GraphicsDevice graphicsDevice)
        {
            pointManager.InitBuffers(graphicsDevice);
        }

        public override void Render(GraphicsDevice graphicsDevice)
        {
            base.Render(graphicsDevice);
            if (IsInitialized == false)
                return;

            pointManager.Render(graphicsDevice);
        }
    }
}
