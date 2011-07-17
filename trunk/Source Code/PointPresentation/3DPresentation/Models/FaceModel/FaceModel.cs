using System;
using System.Collections.Generic;
using System.IO;
using Microsoft.Xna.Framework;
using Microsoft.Xna.Framework.Graphics;
using _3DPresentation.Material;
using System.Windows.Media.Imaging;

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
            NumPoints = faceManager.NumPoints;
            NumFaces = faceManager.NumFaces;
        }

        public override void InitBuffers(GraphicsDevice graphicsDevice)
        {
            faceManager.InitBuffers(graphicsDevice);
        }

        public override void Render(GraphicsDevice graphicsDevice, bool specialRender)
        {
            base.Render(graphicsDevice, specialRender);
            if (IsInitialized == false)
                return;

            faceManager.Render(graphicsDevice);
        }

        protected override bool ExportVertexData(FileType fileType, VertexTypes vertexType, StreamWriter writer, bool keepOriginalPosition)
        {
            if (writer == null)
                return false;
            if (fileType == FileType.PLY)
            {
                if (keepOriginalPosition)
                    return faceManager.ExportVertexData(fileType, vertexType, writer, Matrix.Identity);
                else
                    return faceManager.ExportVertexData(fileType, vertexType, writer, WorldMatrix);
            }
            return false;
        }

        protected override bool ExportIndiceData(FileType fileType, VertexTypes vertexType, StreamWriter writer, long offset)
        {
            if (writer == null)
                return false;
            if (fileType == FileType.PLY)
                return faceManager.ExportIndiceData(fileType, vertexType, writer, WorldMatrix, offset);
            return false;
        }

        protected override BaseMaterial GetDefaultMaterial()
        {
            return new SimpleEffectMaterial();
        }

        protected override BaseMaterial GetDefaultSpecialMaterial()
        {
            return new SimpleEffectMaterial();
        }

        public override Type[] GetCompatibleMaterialTypes()
        {
            Type[] compatibleTypes = new Type[]
            {
                typeof(SimpleEffectMaterial),
                //typeof(TexturedNoEffectMaterial),
                typeof(FourPointLightsMaterial),
                typeof(VertexColorMaterial)
            };
            return compatibleTypes;
        }

        public override System.Windows.Media.Imaging.WriteableBitmap toBitmap(int iWidth, int iHeight, Babylon.Toolbox.OrbitCamera cam)
        {
            //return new WriteableBitmap(0, 0).FromResource("Views/Editor/Images/blank_facemodel.jpg");

            System.Windows.Media.Imaging.WriteableBitmap wbm = new System.Windows.Media.Imaging.WriteableBitmap(400, 400);//.FromResource("Views/Editor/Images/blank.jpg");
            System.Windows.Media.Imaging.WriteableBitmapExtensions.Clear(wbm, System.Windows.Media.Color.FromArgb(255, 0, 0, 0));
            Matrix mat = cam.View * cam.Projection;

            int[,] zbuffer = new int[iWidth, iHeight];

            faceManager.projectToImagePlane(mat, iWidth, iHeight, zbuffer, wbm);
            return wbm;
        }
    }
}
