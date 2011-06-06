
using Microsoft.Xna.Framework;
namespace _3DPresentation
{
    public struct Camera
    {
        public Matrix view; // The view or camera transform
        public Matrix projection; // The projection transform to convert 3D space to 2D screen space
        public Vector3 cameraPosition; // the camera's position
        public Vector3 cameraTarget;
    }
}
