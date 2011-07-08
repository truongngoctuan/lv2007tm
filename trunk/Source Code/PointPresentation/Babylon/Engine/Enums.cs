namespace Babylon
{
    public enum InheritTypes
    {
        /// <summary>
        /// Inherits Position, rotation and scaling.
        /// </summary>
        All,
        /// <summary>
        /// Inherits position only.
        /// </summary>
        OnlyPosition
    }

    public enum LightType
    {
        /// <summary>
        /// Point light.
        /// </summary>
        Point = 1,
        /// <summary>
        /// Spot light.
        /// </summary>
        Spot = 2,
        /// <summary>
        /// Directional light.
        /// </summary>
        Directional = 3,
    }

    public enum MoveDirection
    {
        Left,
        Right,
        Forward,
        Backward
    }

    public enum StreamingState
    {
        PreLoaded,
        Loading,
        Loaded,
    }
}
