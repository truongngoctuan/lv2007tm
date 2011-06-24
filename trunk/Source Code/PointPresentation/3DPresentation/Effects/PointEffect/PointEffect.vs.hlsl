// transformation matrix provided by the application
float4x4 WorldViewProjection;
// Scale should be (2f / drawingSurface.Width, 2f / drawingSurface.Height, 0, 0)
float4 Scale;

// vertex input to the shader
struct VertexData
{
  float3 Position : POSITION;
  float2 Offset : POSITION1;
  float4 Color : COLOR;
};

// vertex shader output passed through to geometry 
// processing and a pixel shader
struct VertexShaderOutput
{
  float4 Position : POSITION;
  float4 Color : COLOR;
};

// main shader function
VertexShaderOutput main(VertexData vertex)
{
  VertexShaderOutput output;

  // apply standard transformation for rendering
  float4 tmp = mul(float4(vertex.Position,1), WorldViewProjection);
  float4 tmp2 = {tmp.x + (vertex.Offset.x * Scale.x * tmp.w), tmp.y + (vertex.Offset.y * Scale.y * tmp.w), tmp.z, tmp.w};
  output.Position = tmp2; 
    
  // pass the color through to the next stage  
  output.Color = vertex.Color; 

  return output;
}
