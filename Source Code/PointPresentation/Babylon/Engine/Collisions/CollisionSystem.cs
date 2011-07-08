using System;
using Microsoft.Xna.Framework;

namespace Babylon
{
    internal class CollisionSystem
    {
        internal Vector3 Radius;
        internal Vector3 InitialVelocity;
        internal Vector3 InitialPosition;
        Vector3 velocity = Vector3.Zero;
        Vector3 normalizedVelocity = Vector3.Zero;
        Vector3 basePoint = Vector3.Zero;
        Vector3 velocityWorld = Vector3.Zero;
        float velocityWorldLength;
        Vector3 basePointWorld = Vector3.Zero;
        float epsilon;
        float nearestDistance;
        internal Vector3 IntersectionPoint = Vector3.Zero;

        internal int Retry { get; set; }
        internal bool CollisionFound { get; private set; }

        public static bool IntersectBoxAASphere(Vector3 boxMin, Vector3 boxMax, Vector3 sphereCenter, float sphereRadius)
        {
            Vector3 boxMinSphere = new Vector3(sphereCenter.X - sphereRadius, sphereCenter.Y - sphereRadius, sphereCenter.Z - sphereRadius);
            Vector3 boxMaxSphere = new Vector3(sphereCenter.X + sphereRadius, sphereCenter.Y + sphereRadius, sphereCenter.Z + sphereRadius);

            if (boxMin.X > boxMaxSphere.X)
                return false;

            if (boxMinSphere.X > boxMax.X)
                return false;

            if (boxMin.Y > boxMaxSphere.Y)
                return false;

            if (boxMinSphere.Y > boxMax.Y)
                return false;

            if (boxMin.Z > boxMaxSphere.Z)
                return false;

            if (boxMinSphere.Z > boxMax.Z)
                return false;

            return true;
        }

        internal void Initialize(Vector3 source, Vector3 dir, float e)
        {
            velocity = dir;
            normalizedVelocity = Vector3.Normalize(velocity);
            basePoint = source;

            basePointWorld = basePoint * Radius;

            velocityWorld = velocity * Radius;

            velocityWorldLength = velocityWorld.Length();

            epsilon = e;
            CollisionFound = false;
        }

        internal Matrix TransformationMatrix
        {
            get
            {
                return Matrix.CreateScale(1.0f / Radius.X, 1.0f / Radius.Y, 1.0f / Radius.Z);
            }
        }

        public static bool CheckPointInTriangle(Vector3 point, Vector3 pa, Vector3 pb, Vector3 pc, Vector3 n)
        {
            Vector3 e0 = pa - point;
            Vector3 e1 = pb - point;

            float d = Vector3.Dot(Vector3.Cross(e0, e1), n);
            if (d < 0)
                return false;
            Vector3 e2 = pc - point;
            d = Vector3.Dot(Vector3.Cross(e1, e2), n);
            if (d < 0)
                return false;
            d = Vector3.Dot(Vector3.Cross(e2, e0), n);
            return d >= 0;
        }

        internal bool CanDoCollision(Vector3 sphereCenter, float sphereRadius, Vector3 vecMin, Vector3 vecMax)
        {
            Vector3 vecTest = basePointWorld - sphereCenter;
            float distance = vecTest.Length();

            float max = Math.Max(Radius.X, Radius.Y);
            max = Math.Max(max, Radius.Z);

            if (distance > velocityWorldLength + max + sphereRadius)
            {
                return false;
            }

            if (!IntersectBoxAASphere(vecMin, vecMax, basePointWorld, velocityWorldLength + max))
                return false;

            return true;
        }

        static bool GetLowestRoot(float a, float b, float c, float maxR, out float root)
        {
            float determinant = b * b - 4.0f * a * c;
            root = 0;

            if (determinant < 0)
                return false;

            float sqrtD = (float)Math.Sqrt(determinant);
            float r1 = (-b - sqrtD) / (2.0f * a);
            float r2 = (-b + sqrtD) / (2.0f * a);

            if (r1 > r2)
            {
                float temp = r2;
                r2 = r1;
                r1 = temp;
            }

            if (r1 > 0 && r1 < maxR)
            {
                root = r1;
                return true;
            }

            if (r2 > 0 && r2 < maxR)
            {
                root = r2;
                return true;
            }

            return false;
        }

        internal void Collide(SubModel subobject, Vector3[] pts, int[] indices, int faceStart, int faceEnd, int decal)
        {
            for (int i = faceStart; i < faceEnd; i++)
            {
                Vector3 p1 = pts[Math.Max(0, indices[i * 3] - decal)];
                Vector3 p2 = pts[Math.Max(0, indices[i * 3 + 1] - decal)];
                Vector3 p3 = pts[Math.Max(0, indices[i * 3 + 2] - decal)];

                TestTriangle(subobject, p1, p2, p3);
            }
        }

        void TestTriangle(SubModel subobject, Vector3 p1, Vector3 p2, Vector3 p3)
        {
            float t0;
            bool embeddedInPlane = false;

            CollisionPlane trianglePlane = new CollisionPlane(p1, p2, p3);

            if ((subobject.Material == null) && !trianglePlane.IsFrontFacingTo(normalizedVelocity, 0))
                return;

            float signedDistToTrianglePlane = trianglePlane.SignedDistanceTo(basePoint);
            float normalDotVelocity = Vector3.Dot(trianglePlane.normal, velocity);

            if (normalDotVelocity == 0)
            {
                if (Math.Abs(signedDistToTrianglePlane) >= 1.0)
                    return;
                embeddedInPlane = true;
                t0 = 0;
            }
            else
            {
                t0 = (-1.0f - signedDistToTrianglePlane) / normalDotVelocity;
                float t1 = (1.0f - signedDistToTrianglePlane) / normalDotVelocity;

                if (t0 > t1)
                {
                    float temp = t1;
                    t1 = t0;
                    t0 = temp;
                }

                if (t0 > 1.0f || t1 < 0.0f)
                    return;

                if (t0 < 0)
                    t0 = 0;
                if (t0 > 1.0f)
                    t0 = 1.0f;
            }

            Vector3 collisionPoint = Vector3.Zero;

            bool found = false;
            float t = 1.0f;

            if (!embeddedInPlane)
            {
                Vector3 planeIntersectionPoint = (basePoint - trianglePlane.normal) + velocity * t0;

                if (CheckPointInTriangle(planeIntersectionPoint, p1, p2, p3, trianglePlane.normal))
                {
                    found = true;
                    t = t0;
                    collisionPoint = planeIntersectionPoint;
                }
            }

            if (!found)
            {
                float velocitySquaredLength = velocity.LengthSquared();
                float newT;

                float a = velocitySquaredLength;

                float b = 2.0f * (Vector3.Dot(velocity, basePoint - p1));
                float c = (p1 - basePoint).LengthSquared() - 1.0f;

                if (GetLowestRoot(a, b, c, t, out newT))
                {
                    t = newT;
                    found = true;
                    collisionPoint = p1;
                }

                b = 2.0f * (Vector3.Dot(velocity, basePoint - p2));
                c = (p2 - basePoint).LengthSquared() - 1.0f;

                if (GetLowestRoot(a, b, c, t, out newT))
                {
                    t = newT;
                    found = true;
                    collisionPoint = p2;
                }

                b = 2.0f * (Vector3.Dot(velocity, basePoint - p3));
                c = (p3 - basePoint).LengthSquared() - 1.0f;

                if (GetLowestRoot(a, b, c, t, out newT))
                {
                    t = newT;
                    found = true;
                    collisionPoint = p3;
                }

                Vector3 edge = p2 - p1;
                Vector3 baseToVertex = p1 - basePoint;
                float edgeSquaredLength = edge.LengthSquared();
                float edgeDotVelocity = Vector3.Dot(edge, velocity);
                float edgeDotBaseToVertex = Vector3.Dot(edge, baseToVertex);

                a = edgeSquaredLength * (-velocitySquaredLength) + edgeDotVelocity * edgeDotVelocity;
                b = edgeSquaredLength * (2.0f * Vector3.Dot(velocity, baseToVertex)) - 2.0f * edgeDotVelocity * edgeDotBaseToVertex;
                c = edgeSquaredLength * (1.0f - baseToVertex.LengthSquared()) + edgeDotBaseToVertex * edgeDotBaseToVertex;
                if (GetLowestRoot(a, b, c, t, out newT))
                {
                    float f = (edgeDotVelocity * newT - edgeDotBaseToVertex) / edgeSquaredLength;

                    if (f >= 0.0f && f <= 1.0f)
                    {
                        t = newT;
                        found = true;
                        collisionPoint = p1 + f * edge;
                    }
                }

                edge = p3 - p2;
                baseToVertex = p2 - basePoint;
                edgeSquaredLength = edge.LengthSquared();
                edgeDotVelocity = Vector3.Dot(edge, velocity);
                edgeDotBaseToVertex = Vector3.Dot(edge, baseToVertex);

                a = edgeSquaredLength * (-velocitySquaredLength) + edgeDotVelocity * edgeDotVelocity;
                b = edgeSquaredLength * (2.0f * Vector3.Dot(velocity, baseToVertex)) - 2.0f * edgeDotVelocity * edgeDotBaseToVertex;
                c = edgeSquaredLength * (1.0f - baseToVertex.LengthSquared()) + edgeDotBaseToVertex * edgeDotBaseToVertex;
                if (GetLowestRoot(a, b, c, t, out newT))
                {
                    float f = (edgeDotVelocity * newT - edgeDotBaseToVertex) / edgeSquaredLength;

                    if (f >= 0.0f && f <= 1.0f)
                    {
                        t = newT;
                        found = true;
                        collisionPoint = p2 + f * edge;
                    }
                }

                edge = p1 - p3;
                baseToVertex = p3 - basePoint;
                edgeSquaredLength = edge.LengthSquared();
                edgeDotVelocity = Vector3.Dot(edge, velocity);
                edgeDotBaseToVertex = Vector3.Dot(edge, baseToVertex);

                a = edgeSquaredLength * (-velocitySquaredLength) + edgeDotVelocity * edgeDotVelocity;
                b = edgeSquaredLength * (2.0f * Vector3.Dot(velocity, baseToVertex)) - 2.0f * edgeDotVelocity * edgeDotBaseToVertex;
                c = edgeSquaredLength * (1.0f - baseToVertex.LengthSquared()) + edgeDotBaseToVertex * edgeDotBaseToVertex;
                if (GetLowestRoot(a, b, c, t, out newT))
                {
                    float f = (edgeDotVelocity * newT - edgeDotBaseToVertex) / edgeSquaredLength;

                    if (f >= 0.0f && f <= 1.0f)
                    {
                        t = newT;
                        found = true;
                        collisionPoint = p3 + f * edge;
                    }
                }
            }

            if (found)
            {
                float distToCollision = t * velocity.Length();

                if (!CollisionFound || distToCollision < nearestDistance)
                {
                    lock (this)
                    {
                        nearestDistance = distToCollision;
                        IntersectionPoint = collisionPoint;
                        CollisionFound = true;
                    }
                }
            }
        }

        internal void GetResponse(ref Vector3 pos, ref Vector3 vel)
        {
            Vector3 destinationPoint = pos + vel;
            Vector3 V = vel * (nearestDistance / vel.Length());

            pos = basePoint + V;
            Vector3 slidePlaneNormal = pos - IntersectionPoint;
            slidePlaneNormal.Normalize();
            Vector3 displacementVector = slidePlaneNormal * epsilon;

            pos = pos + displacementVector;
            IntersectionPoint = IntersectionPoint + displacementVector;

            Vector3 slidePlaneOrigin = IntersectionPoint;
            CollisionPlane slidingPlane = new CollisionPlane(slidePlaneOrigin, slidePlaneNormal);
            Vector3 newDestinationPoint = destinationPoint - slidePlaneNormal * slidingPlane.SignedDistanceTo(destinationPoint);

            vel = newDestinationPoint - IntersectionPoint;
        }
    }
}
