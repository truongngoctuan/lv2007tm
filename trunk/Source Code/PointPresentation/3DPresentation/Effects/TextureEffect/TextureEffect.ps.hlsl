float4 xDiffuseSource1;
float4 xDiffuseColor1;

float4 xDiffuseSource2;
float4 xDiffuseColor2;

float4 xDiffuseSource3;
float4 xDiffuseColor3;

float4 xDiffuseIntensity;

float4 xAmbientIntensity;
// vertex shader output passed through to geometry 
// processing and a pixel shader
struct VertexShaderOutput
{
  float4 Position : POSITION;
  float2 TextureCoords		: TEXCOORD0;
  float3 Normal        : TEXCOORD1;
  float3 Position3D    : TEXCOORD2;  
};

struct PixelToFrame
{
    float4 Color        : COLOR;
};

// Samplers
sampler2D DiffuseSampler		: register(s0);

PixelToFrame main(VertexShaderOutput PSIn)
{
    PixelToFrame Output = (PixelToFrame)0; 

	// Ambient
	float4 baseColor = tex2D(DiffuseSampler, float2(PSIn.TextureCoords.x, PSIn.TextureCoords.y));
	float4 effectColor = float4(1.0f, 1.0f, 1.0f, 1.0f) * (float)xAmbientIntensity;

	if(PSIn.TextureCoords.x == 0)
	{
	// Diffuse
	// Determine the diffuse component by finding the angle between the light and the normal.
	// The smaller the angle between the normal and the light direction, the closer the dot
	// product will be to 1, and the brighter the pixel will be.
	if(xDiffuseIntensity.x > 0)
	{
		float lightIntensity = xDiffuseIntensity.x;
		float3 lightDirection = normalize(PSIn.Position3D - (float3)xDiffuseSource1);
		float factor = (dot(-lightDirection, PSIn.Normal));
		factor *= max(0,(1 - pow(distance((float3)xDiffuseSource1, PSIn.Position3D) / lightIntensity, 2)));
		if(lightIntensity > 0.0f)
		{
			float4 diffuse = xDiffuseColor1 * factor;
			effectColor = (diffuse + effectColor);
		}
	}

	if(xDiffuseIntensity.y > 0)
	{
		float lightIntensity = xDiffuseIntensity.y;
		float3 lightDirection = normalize(PSIn.Position3D - (float3)xDiffuseSource2);
		float factor = (dot(-lightDirection, PSIn.Normal));
		factor *= max(0,(1 - pow(distance((float3)xDiffuseSource2, PSIn.Position3D) / lightIntensity, 2)));
		if(lightIntensity > 0.0f)
		{
			float4 diffuse = xDiffuseColor2 * factor;
			effectColor = (diffuse + effectColor);
		}
	}

	if(xDiffuseIntensity.z > 0)
	{
		float lightIntensity = xDiffuseIntensity.z;
		float3 lightDirection = normalize(PSIn.Position3D - (float3)xDiffuseSource3);
		float factor = (dot(-lightDirection, PSIn.Normal));
		factor *= max(0,(1 - pow(distance((float3)xDiffuseSource3, PSIn.Position3D) / lightIntensity, 2)));
		if(lightIntensity > 0.0f)
		{
			float4 diffuse = xDiffuseColor3 * factor;
			effectColor = (diffuse + effectColor);
		}
	}

	effectColor = saturate(effectColor);
	Output.Color = (baseColor * effectColor);
	}
	else
	Output.Color = baseColor;
    return Output;
}
