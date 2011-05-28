// ===================================================================================
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//  THIS CODE AND INFORMATION IS PROVIDED "AS IS" WITHOUT WARRANTY
//  OF ANY KIND, EITHER EXPRESSED OR IMPLIED, INCLUDING BUT NOT
//  LIMITED TO THE IMPLIED WARRANTIES OF MERCHANTABILITY AND
//  FITNESS FOR A PARTICULAR PURPOSE.
// ===================================================================================

// This simple pixel shader returns the unmodified vertex color.
// ---

float4 xLightSource : register(c0);
float4 xLightIntensity : register(c1);
float4 xDiffuseColor  : register(c2);
float4 xAmbientIntensity  : register(c3);

// vertex shader output passed through to geometry 
// processing and a pixel shader
struct VertexShaderOutput
{
  float4 Position : POSITION;
  float4 Color : COLOR;  
  float3 Normal        : TEXCOORD0;
  float3 Position3D    : TEXCOORD1;  
};

struct PixelToFrame
{
    float4 Color        : COLOR;
};

PixelToFrame main(VertexShaderOutput PSIn)
{
    PixelToFrame Output = (PixelToFrame)0;    

	// Ambient
	float4 baseColor = PSIn.Color;
	float4 effectColor = float4(1.0f, 1.0f, 1.0f, 1.0f) * (float)xAmbientIntensity;

	// Disfuse
	// Determine the diffuse component by finding the angle between the light and the normal.
    // The smaller the angle between the normal and the light direction, the closer the dot
    // product will be to 1, and the brighter the pixel will be.
	float3 lightDirection = normalize(PSIn.Position3D - (float3)xLightSource);
	float lightIntensity = saturate(dot(-lightDirection, PSIn.Normal)) * (1 - distance((float3)xLightSource, PSIn.Position3D) / xLightIntensity);
	if(lightIntensity > 0.0f)
	{
		float4 diffuse = xDiffuseColor * lightIntensity;
		effectColor = saturate(diffuse + effectColor);
	}
	
	Output.Color = saturate(baseColor * effectColor);
	//Output.Color = effectColor;
	// Apply
	//Output.Color = PSIn.Color;
    return Output;
}
