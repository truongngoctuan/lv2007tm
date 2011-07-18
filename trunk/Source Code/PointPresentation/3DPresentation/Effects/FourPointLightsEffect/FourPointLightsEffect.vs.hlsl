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
float4x4 World;

float4 LightSource1;
float4 LightSource2;
float4 LightSource3;
float4 LightSource4;

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
  float3 LightDir1 : TEXCOORD1;
  float3 LightDir2 : TEXCOORD2;
  float3 LightDir3 : TEXCOORD3;
  float3 LightDir4 : TEXCOORD4;
};

// main shader function
VertexShaderOutput main(VertexData vertex)
{
	VertexShaderOutput Output = (VertexShaderOutput)0;

    Output.Position = mul(float4(vertex.Position,1), WorldViewProjection);
    Output.Color = vertex.Color;
	
	// Calculate the normal vector against the world matrix only.
    Output.Normal = mul(vertex.Normal, (float3x3)World);
	
    // Normalize the normal vector.
    Output.Normal = normalize(Output.Normal);

    // Calculate the position of the vertex in the world.
    float4 worldPosition = mul(float4(vertex.Position, 1.0f), World);

	// Determine the light directions based on the position of the lights and the position of the vertex in the world.
	// Normalize the light position vectors.
    Output.LightDir1 = normalize(LightSource1.xyz - worldPosition.xyz);
    Output.LightDir2 = normalize(LightSource2.xyz - worldPosition.xyz);
    Output.LightDir3 = normalize(LightSource3.xyz - worldPosition.xyz);
    Output.LightDir4 = normalize(LightSource4.xyz - worldPosition.xyz);
    return Output;
}