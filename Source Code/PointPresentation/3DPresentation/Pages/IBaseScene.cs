using System;
using Microsoft.Xna.Framework;
using Babylon.Toolbox;


namespace _3DPresentation
{
    public interface IBaseScene
    {
        Vector3 GetCameraPosition();
        Matrix GetCameraView();
        Matrix GetCameraProjection();

        Vector2 GetDrawingSurfaceSize();

        StatesManager GetStatesManager();
    }
}
