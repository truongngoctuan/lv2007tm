using System;
using System.Collections.Generic;
using System.IO;
using Microsoft.Xna.Framework;
using Microsoft.Xna.Framework.Graphics;
using _3DPresentation.Material;
using System.Windows.Media.Imaging;

namespace _3DPresentation.Models
{
    public class TexCoordModel : BaseModel
    {
        // component
        TexCoordManager texCoordManager;

        public TexCoordModel()
        {
            texCoordManager = new TexCoordManager(this);
        }

        public override void Begin(int nPoints, int nFaces)
        {
            base.Begin(nPoints, nFaces);
            texCoordManager.Begin(nPoints, nFaces);
        }
        public override void AddVertex(Vector3 position, Color color)
        {
            base.AddVertex(position, color);
            texCoordManager.AddVertex(position);
        }
        public override void AddVertex(Vector3 position)
        {
            base.AddVertex(position);
            texCoordManager.AddVertex(position);
        }
        public override void AddVertex(Vector3 position, Vector3 normal)
        {
            base.AddVertex(position, normal);
            texCoordManager.AddVertex(position, normal);
        }
        public override void AddIndice(int i1, int i2, int i3)
        {
            base.AddIndice(i1, i2, i3);
        }
        public override void AddIndice(int i1, int i2, int i3, Vector2 texCoord1, Vector2 texCoord2, Vector2 texCoord3)
        {
            base.AddIndice(i1, i2, i3);
            texCoordManager.AddIndice(i1, i2, i3, texCoord1, texCoord2, texCoord3);
        }
        public override void End()
        {
            base.End();
            texCoordManager.End();
            NumPoints = texCoordManager.NumPoints;
            NumFaces = texCoordManager.NumFaces;
        }

        public override void InitBuffers(GraphicsDevice graphicsDevice)
        {
            texCoordManager.InitBuffers(graphicsDevice);
        }

        public override void Render(GraphicsDevice graphicsDevice, bool specialRender)
        {
            base.Render(graphicsDevice, specialRender);
            if (IsInitialized == false)
                return;

            texCoordManager.Render(graphicsDevice);
        }

        protected override bool ExportVertexData(FileType fileType, VertexTypes vertexType, StreamWriter writer, bool keepOriginalPosition)
        {
            if (writer == null)
                return false;
            if (fileType == FileType.PLY)
            {
                if (keepOriginalPosition)
                    return texCoordManager.ExportVertexData(fileType, vertexType, writer, Matrix.Identity);
                else
                    return texCoordManager.ExportVertexData(fileType, vertexType, writer, WorldMatrix);
            }                
            return false;
        }

        protected override bool ExportIndiceData(FileType fileType, VertexTypes vertexType, StreamWriter writer, long offset)
        {
            if (writer == null)
                return false;
            if (fileType == FileType.PLY)
                return texCoordManager.ExportIndiceData(fileType, vertexType, writer, WorldMatrix, offset);
            return false;
        }

        protected override BaseMaterial GetDefaultMaterial()
        {
            return new TextureMaterial();
        }

        protected override BaseMaterial GetDefaultSpecialMaterial()
        {
            return Material;
            //return new TextureMaterial();
        }

        public override Type[] GetCompatibleMaterialTypes()
        {
            Type[] compatibleTypes = new Type[]
            {
                typeof(TextureMaterial),
                //typeof(FourPointLightsTextureMaterial),
                typeof(BasicMaterial)
            };
            return compatibleTypes;
        }

        public override System.Windows.Media.Imaging.WriteableBitmap toBitmap()
        {
            return base.toBitmap();
        }

        public override System.Windows.Media.Imaging.WriteableBitmap toBitmap(int iWidth, int iHeight, Babylon.Toolbox.OrbitCamera cam, float k)
        {
            System.Windows.Media.Imaging.WriteableBitmap wbm = new System.Windows.Media.Imaging.WriteableBitmap(iWidth, iHeight);//.FromResource("Views/Editor/Images/blank.jpg");
            System.Windows.Media.Imaging.WriteableBitmapExtensions.Clear(wbm, System.Windows.Media.Color.FromArgb(255, 0, 0, 0));
            Matrix mat = cam.View * cam.Projection;

            int[,] zbuffer = new int[iWidth, iHeight];

            texCoordManager.projectToImagePlane(mat, iWidth, iHeight, zbuffer, wbm, k);
            return wbm;
        }
    }
}
