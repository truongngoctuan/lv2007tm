// ===================================================================================
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//  THIS CODE AND INFORMATION IS PROVIDED "AS IS" WITHOUT WARRANTY
//  OF ANY KIND, EITHER EXPRESSED OR IMPLIED, INCLUDING BUT NOT
//  LIMITED TO THE IMPLIED WARRANTIES OF MERCHANTABILITY AND
//  FITNESS FOR A PARTICULAR PURPOSE.
// ===================================================================================

// This simple pixel shader returns the unmodified vertex color.
// ---

sampler2D DiffuseSampler		: register(s0);
// output from the vertex shader serves as input
// to the pixel shader
struct VertexShaderOutput
{
  float4 Position : POSITION;
  float4 Color : COLOR;
  float2 textureCoords : TEXCOORD0;
};

// main shader function
float4 main(VertexShaderOutput vertex) : COLOR
{
	float2 textureCoords = float2(vertex.textureCoords.x, vertex.textureCoords.y);
	//textureCoords += vertex.textureCoords;

	float4 color = float4(tex2D(DiffuseSampler, textureCoords).rgb, 1.0f);
	return color;
}