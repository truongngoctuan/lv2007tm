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
float4x4 xWorldViewProjection;
float4x4 xWorld;

// vertex input to the shader matching the structure
// defined in the application
struct VertexData
{
	// DOES NOT NEED TO BE IN THE SAME ORDER
	// BUT MUST MATCH THE DESCRIPTION : Position, Normal, Color, TEXCOORD.... in VertexDeclaration
  float3 Position : POSITION;    
  float3 Normal : NORMAL;
  float4 Color : COLOR;  
};

// vertex shader output passed through to geometry 
// processing and a pixel shader
struct VertexShaderOutput
{
  float4 Position : POSITION;
  float4 Color : COLOR;  
  float3 Normal : TEXCOORD0;
  float3 Position3D    : TEXCOORD1;  
};

// main shader function
VertexShaderOutput main(VertexData vertex)
{
	VertexShaderOutput Output = (VertexShaderOutput)0;

    Output.Position = mul(float4(vertex.Position,1), xWorldViewProjection);
    Output.Color = vertex.Color;

	Output.Normal = normalize(mul(normalize(vertex.Normal), (float3x3)xWorld));    
	Output.Position3D = mul(vertex.Position, xWorld);
	//if(vertex.Position.z > -1000)
		//Output.Color = 1;
    return Output;
}