using Microsoft.Xna.Framework;

namespace Babylon
{
	public partial class Model
	{
        public bool CheckCollisions { get; set; }

		internal void CheckCollision(CollisionSystem system)
		{
			// Bounding box test
			if (!BoundingInfo.CheckCollision(system))
				return;

			// Transformation matrix
			Matrix transformMatrix = world * system.TransformationMatrix;

			ProcessCollisionsForSubModels(system, transformMatrix, 0, subModels.Count);
		}

		void CollideForSubModel(SubModel subModel, Matrix transformMatrix, CollisionSystem collider)
		{
			// Transformation
			if ((!subModel.WorldVertices.ContainsKey(collider)) || (subModel.TransformationMatrices[collider] != transformMatrix))
			{
				if (!subModel.WorldVertices.ContainsKey(collider) || subModel.WorldVertices[collider].Length != subModel.PositionOnlyVertexCount)
				{
					if (subModel.WorldVertices.ContainsKey(collider))
						subModel.WorldVertices.Remove(collider);

					subModel.WorldVertices.Add(collider, new Vector3[subModel.PositionOnlyVertexCount]);
				}

				if (subModel.TransformationMatrices.ContainsKey(collider))
					subModel.TransformationMatrices.Remove(collider);

				subModel.TransformationMatrices.Add(collider, transformMatrix);

				Vector3[] vertices = subModel.WorldVertices[collider];

				for (int i = subModel.PositionOnlyVertexStart; i < subModel.PositionOnlyVertexStart + subModel.PositionOnlyVertexCount; i++)
				{
					vertices[i - subModel.PositionOnlyVertexStart] = Vector3.Transform(Points[i], transformMatrix);
				}
			}

			// Collide
			collider.Collide(subModel, subModel.WorldVertices[collider], Indices, subModel.StartIndex / 3, subModel.StartIndex / 3 + subModel.FacesCount, subModel.PositionOnlyVertexStart);
		}

		private void ProcessCollisionsForSubModels(CollisionSystem collider, Matrix transformMatrix, int start, int end)
		{
			for (int index = start; index < end; index++)
			{
				SubModel subModel = subModels[index];

				// Bounding test
                if (subModels.Count > 1 && !subModel.BoundingInfo.CheckCollision(collider))
					continue;

				CollideForSubModel(subModel, transformMatrix, collider);

			}
		}
	}
}