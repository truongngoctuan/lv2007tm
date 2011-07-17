using System;
using System.Collections.Generic;
using System.IO;
using Microsoft.Xna.Framework;
using Microsoft.Xna.Framework.Graphics;
using _3DPresentation.Material;
using System.Windows.Media.Imaging;

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

        public override void Render(GraphicsDevice graphicsDevice, bool specialRender)
        {
            base.Render(graphicsDevice, specialRender);
            if (IsInitialized == false)
                return;

            pointManager.Render(graphicsDevice);
        }

        protected override bool ExportVertexData(FileType fileType, VertexTypes vertexType, StreamWriter writer, bool keepOriginalPosition)
        {
            if (writer == null)
                return false;
            if (fileType == FileType.PLY)
            {
                if (keepOriginalPosition)
                    return pointManager.ExportVertexData(fileType, vertexType, writer, Matrix.Identity);
                else
                    return pointManager.ExportVertexData(fileType, vertexType, writer, WorldMatrix);
            }
                
            return false;
        }

        protected override bool ExportIndiceData(FileType fileType, VertexTypes vertexType, StreamWriter writer, long offset)
        {
            if (writer == null)
                return false;
            if(fileType == FileType.PLY)
                return pointManager.ExportIndiceData(fileType, vertexType, writer, WorldMatrix, offset);
            return false;
        }

        protected override BaseMaterial GetDefaultMaterial()
        {
            return new PointMaterial();
        }

        protected override BaseMaterial GetDefaultSpecialMaterial()
        {
            return Material;
            //return new PointMaterial();
        }

        public override Type[] GetCompatibleMaterialTypes()
        {
            Type[] compatibleTypes = new Type[]
            {
                typeof(PointMaterial)
            };
            return compatibleTypes;
        }

        public override System.Windows.Media.Imaging.WriteableBitmap toBitmap(int iWidth, int iHeight, Babylon.Toolbox.OrbitCamera cam)
        {
            System.Windows.Media.Imaging.WriteableBitmap wbm = new System.Windows.Media.Imaging.WriteableBitmap(iWidth, iHeight);//.FromResource("Views/Editor/Images/blank.jpg");
            System.Windows.Media.Imaging.WriteableBitmapExtensions.Clear(wbm, System.Windows.Media.Color.FromArgb(255, 0, 0, 0));
            Matrix mat = cam.View * cam.Projection;

            int[,] zbuffer = new int[iWidth, iHeight];

            pointManager.projectToImagePlane(mat, iWidth, iHeight, zbuffer, wbm);
            return wbm;
        }
    }
}
