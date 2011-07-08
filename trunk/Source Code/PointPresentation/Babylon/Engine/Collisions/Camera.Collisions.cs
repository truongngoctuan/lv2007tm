using Microsoft.Xna.Framework;

namespace Babylon
{
	public partial class Camera
	{
	    readonly CollisionSystem collider = new CollisionSystem();
	    public bool CheckCollisions { get; set; }
	    internal Vector3 Ellipsoid { get; set; }
	    internal Vector3 EllipsoidOffset;
	    public float CollisionsEpsilon { get; set; }

	    public void Move(Vector3 velocity)
		{
			if (CheckCollisions && Scene.CheckCollisions)
			{
				CheckCollisions = false;
                Vector3 oldPosition = Position + EllipsoidOffset;
				collider.Radius = Ellipsoid;

				Vector3 newPosition = Scene.GetNewPosition(oldPosition, velocity, collider, 3);
				Vector3 diffPosition = newPosition - oldPosition;

				if (diffPosition.Length() > CollisionsEpsilon)
                    Position += diffPosition;
				CheckCollisions = true;
			}
			else
			{
				Position += velocity;
			}
		}
	}
}
