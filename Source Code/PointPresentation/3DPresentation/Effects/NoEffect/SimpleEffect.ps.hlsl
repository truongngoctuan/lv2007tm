float4 AmbientColor;

// to the pixel shader
struct VertexShaderOutput
{
  float4 Position : POSITION;
  float4 Color : COLOR;
};

// main shader function
float4 main(VertexShaderOutput vertex) : COLOR
{
	return vertex.Color * AmbientColor;
}