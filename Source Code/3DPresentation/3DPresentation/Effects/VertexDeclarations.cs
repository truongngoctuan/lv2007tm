using Microsoft.Xna.Framework;
using Microsoft.Xna.Framework.Graphics;


/// <summary>
/// Represents a vertex with position and color elements.
/// </summary>
public struct VertexPositionColor
{
    // MUST HAVE THE SAME ORDER as VertexDeclaration
    public Vector3 Position;
    public Color Color;

    public VertexPositionColor(Vector3 position, Color color)
    {
        Position = position;
        Color = color;
    }

    public static readonly VertexDeclaration VertexDeclaration = new VertexDeclaration(
        new VertexElement(0, VertexElementFormat.Vector3, VertexElementUsage.Position, 0),
        new VertexElement(sizeof(float) * 3, VertexElementFormat.Color, VertexElementUsage.Color, 0)
        );
}

public struct VertexPositionNormalColor
{
    // MUST HAVE THE SAME ORDER as VertexDeclaration
    public Vector3 Position;
    public Vector3 Normal;
    public Color Color;

    public VertexPositionNormalColor(Vector3 position, Color color, Vector3 normal)
    {
        Position = position;
        Normal = normal;
        Color = color;
    }

    public static readonly VertexDeclaration VertexDeclaration = new VertexDeclaration(
        new VertexElement(0, VertexElementFormat.Vector3, VertexElementUsage.Position, 0),
        new VertexElement(sizeof(float) * 3, VertexElementFormat.Vector3, VertexElementUsage.Normal, 0),
        new VertexElement(sizeof(float) * (3 + 3), VertexElementFormat.Color, VertexElementUsage.Color, 0)
        );
}
