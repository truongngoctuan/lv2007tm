using Microsoft.Xna.Framework;

namespace Babylon
{
    public partial class Camera : Entity
    {
        readonly Plane[] frustumPlanes = new Plane[6];

        internal void ComputeFrustumPlanes()
        {
            Matrix transform = View * Projection;

            frustumPlanes[0] = new Plane( // near
                transform.M14 + transform.M13,
                transform.M24 + transform.M23,
                transform.M33 + transform.M33,
                transform.M44 + transform.M43);
            frustumPlanes[0].Normalize();

            frustumPlanes[1] = new Plane( // far 
                transform.M14 - transform.M13,
                transform.M24 - transform.M23,
                transform.M34 - transform.M33,
                transform.M44 - transform.M43);
            frustumPlanes[1].Normalize();

            frustumPlanes[2] = new Plane( // left
                transform.M14 + transform.M11,
                transform.M24 + transform.M21,
                transform.M34 + transform.M31,
                transform.M44 + transform.M41);
            frustumPlanes[2].Normalize();

            frustumPlanes[3] = new Plane( // right
                transform.M14 - transform.M11,
                transform.M24 - transform.M21,
                transform.M34 - transform.M31,
                transform.M44 - transform.M41);
            frustumPlanes[3].Normalize();

            frustumPlanes[4] = new Plane( // top
                transform.M14 - transform.M12,
                transform.M24 - transform.M22,
                transform.M34 - transform.M32,
                transform.M44 - transform.M42);
            frustumPlanes[4].Normalize();

            frustumPlanes[5] = new Plane( // bottom
                transform.M14 + transform.M12,
                transform.M24 + transform.M22,
                transform.M34 + transform.M32,
                transform.M44 + transform.M42);
            frustumPlanes[5].Normalize();
        }

        public bool IsInFrustrum(BoundingInfo boundingInfo)
        {
            Vector3 final = boundingInfo.SphereCenterWorld;

            if (!FrustrumCulling(final, boundingInfo.SphereRadiusWorld))
                return false;
            if (!FrustrumCulling(boundingInfo.boundingBoxVectorsWorld))
                return false;

            return true;
        }

        internal bool FrustrumCulling(Vector3 sphereCenter, float radius)
        {
            float length = radius;

            for (int i = 0; i < 6; i++)
            {
                if (frustumPlanes[i].DotCoordinate(sphereCenter) <= -length)
                    return false;
            }

            return true;
        }

        internal bool FrustrumCulling(Vector3[] boxVertices)
        {
            for (int p = 0; p < 6; p++)
            {
                int inCount = 8;

                for (int i = 0; i < 8; i++)
                {
                    if (frustumPlanes[p].DotCoordinate(boxVertices[i]) < 0)
                    {
                        --inCount;
                    }
                    else
                        break;
                }
                if (inCount == 0)
                    return false;
            }
            return true;
        }
    }
}
