using Microsoft.Xna.Framework;

namespace Babylon
{
    public partial class Scene
    {
        public Vector3 Gravity { get; set; }
        public float CollisionEpsilon { get; set; }
        public bool CheckCollisions { get; set; }

        public float UnitPerMeter { get; set; }

        internal Vector3 GetNewPosition(Vector3 position, Vector3 velocity, CollisionSystem collider, int maximumRetry)
        {
            if (!CheckCollisions)
            {
                return position + velocity;
            }

            Vector3 scaledPosition = position / collider.Radius;
            Vector3 scaledVelocity = velocity / collider.Radius;

            collider.Retry = 0;
            collider.InitialVelocity = scaledVelocity;
            collider.InitialPosition = scaledPosition;
            Vector3 finalPosition = CollideWithWorld(scaledPosition, scaledVelocity, collider, maximumRetry);

            finalPosition *= collider.Radius;

            return finalPosition;
        }

        internal Vector3 CollideWithWorld(Vector3 position, Vector3 velocity, CollisionSystem system, int maximumRetry)
        {
            float closeDistance = CollisionEpsilon * UnitPerMeter / 10.0f;

            if (system.Retry >= maximumRetry)
            {
                return position;
            }

            system.Initialize(position, velocity, closeDistance);

            // Check all models
            foreach (Model model in Models)
            {
                if (model.Enabled && model.CheckCollisions)
                {
                    model.CheckCollision(system);
                }
            }

            if (!system.CollisionFound)
            {
                return position + velocity;
            }

            if (velocity.X != 0 || velocity.Y != 0 || velocity.Z != 0)
                system.GetResponse(ref position, ref velocity);

            if (velocity.Length() <= closeDistance)
            {
                return position;
            }

            system.Retry++;
            return CollideWithWorld(position, velocity, system, maximumRetry);
        }
    }
}