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
  float2 TextureCoords : TEXCOORD0;
};

// vertex shader output passed through to geometry 
// processing and a pixel shader
struct VertexShaderOutput
{
  float4 Position : POSITION;
  float2 TextureCoords : TEXCOORD0;
  float3 Normal : TEXCOORD1;
  float3 LightDir1 : TEXCOORD2;
  float3 LightDir2 : TEXCOORD3;
  float3 LightDir3 : TEXCOORD4;
  //float3 LightDir4 : TEXCOORD5;
};

// main shader function
VertexShaderOutput main(VertexData vertex)
{
	VertexShaderOutput Output = (VertexShaderOutput)0;

    Output.Position = mul(float4(vertex.Position,1), WorldViewProjection);
    Output.TextureCoords = vertex.TextureCoords;
	
	// Calculate the normal vector against the world matrix only.
    Output.Normal = mul(vertex.Normal, (float3x3)World);
	
    // Normalize the normal vector.
    Output.Normal = normalize(Output.Normal);

    // Calculate the position of the vertex in the world.
    float4 worldPosition = mul(float4(vertex.Position, 1.0f), World);

	// Determine the light directions based on the position of the lights and the position of the vertex in the world.
    Output.LightDir1.xyz = LightSource1.xyz - worldPosition.xyz;
    Output.LightDir2.xyz = LightSource2.xyz - worldPosition.xyz;
    Output.LightDir3.xyz = LightSource3.xyz - worldPosition.xyz;
    //Output.LightDir4.xyz = LightSource4.xyz - worldPosition.xyz;

    // Normalize the light position vectors.
    Output.LightDir1 = normalize(Output.LightDir1);
    Output.LightDir2 = normalize(Output.LightDir2);
    Output.LightDir3 = normalize(Output.LightDir3);
    //Output.LightDir4 = normalize(Output.LightDir4);
    return Output;
}