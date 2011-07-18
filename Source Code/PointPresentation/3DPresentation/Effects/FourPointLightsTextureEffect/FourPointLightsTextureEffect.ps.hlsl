float4 LightColor1;
float4 LightColor2;
float4 LightColor3;
float4 LightColor4;

float4 EnableLights;
float4 AmbientLight;

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

struct PixelToFrame
{
    float4 Color        : COLOR;
};

// Samplers
sampler2D DiffuseSampler		: register(s0);

PixelToFrame main(VertexShaderOutput input)
{
    PixelToFrame Output = (PixelToFrame)0; 

	float4 textureColor;
    float lightIntensity1, lightIntensity2, lightIntensity3, lightIntensity4;
    float4 color;

	color = AmbientLight;
	if(EnableLights.x > 0.0f)
	{
		// Calculate the different amounts of light on this pixel based on the positions of the lights.
		lightIntensity1 = saturate(dot(input.Normal, input.LightDir1));
		// Determine the diffuse color amount of each of the four lights.
		if(lightIntensity1 > 0.0f)
			color += LightColor1 * float4(lightIntensity1, lightIntensity1, lightIntensity1, 1.0f);
	}

	if(EnableLights.y > 0.0f)
	{		
		// Calculate the different amounts of light on this pixel based on the positions of the lights.
		lightIntensity2 = saturate(dot(input.Normal, input.LightDir2));
		// Determine the diffuse color amount of each of the four lights.
		if(lightIntensity2 > 0.0f)
			color += LightColor2 * float4(lightIntensity2, lightIntensity2, lightIntensity2, 1.0f);
	}

	if(EnableLights.z > 0.0f)
	{
		// Calculate the different amounts of light on this pixel based on the positions of the lights.
		lightIntensity3 = saturate(dot(input.Normal, input.LightDir3));
		// Determine the diffuse color amount of each of the four lights.
		if(lightIntensity3 > 0.0f)
			color += LightColor3 * float4(lightIntensity3, lightIntensity3, lightIntensity3, 1.0f);
	}

	//if(EnableLights.w > 0.0f)
	//{
		//// Calculate the different amounts of light on this pixel based on the positions of the lights.
		//lightIntensity4 = saturate(dot(input.Normal, input.LightDir4));
		//// Determine the diffuse color amount of each of the four lights.
		//if(lightIntensity4 > 0.0f)
			//color += LightColor4 * float4(lightIntensity4, lightIntensity4, lightIntensity4, 1.0f);
	//}

    // Sample the texture pixel at this location.
	textureColor = tex2D(DiffuseSampler, input.TextureCoords);

	// Multiply the texture pixel by the combination of all four light colors to get the final result.
    Output.Color = saturate(color) * textureColor;
	
    return Output;
}
