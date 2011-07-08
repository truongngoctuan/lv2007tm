// ===================================================================================
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//  THIS CODE AND INFORMATION IS PROVIDED "AS IS" WITHOUT WARRANTY
//  OF ANY KIND, EITHER EXPRESSED OR IMPLIED, INCLUDING BUT NOT
//  LIMITED TO THE IMPLIED WARRANTIES OF MERCHANTABILITY AND
//  FITNESS FOR A PARTICULAR PURPOSE.
// ===================================================================================

// This simple vertex shader transforms input vertices to screen space.
// ---

// transformation matrix provided by the application
float4x4 WorldViewProjection;

// vertex input to the shader matching the structure
// defined in the application
struct VertexData
{
  float3 Position : POSITION;
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
  // Position of this point in object coordinate system
  // => need to be transform to camera coordinate
  output.Position = mul(float4(vertex.Position,1), WorldViewProjection);

  // pass the color through to the next stage (pass to pixel shader)
  output.Color = vertex.Color;
  return output;
}