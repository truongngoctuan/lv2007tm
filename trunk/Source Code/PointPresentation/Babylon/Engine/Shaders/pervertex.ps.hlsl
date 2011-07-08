float4 AmbientColor;
float4 DiffuseColor;		

float4 Booleans01;				// x = UseDiffuseTexture, y = UseAmbientTexture, z = DiffuseUseCanal2, w = AmbientUseCanal2
float4 Booleans02;				// x = UseOpacityTexture, y = OpacityUseCanal2, z = AlphaTestEnable

float4 Levels;					// x = DiffuseLevel, y = AmbientLevel

// Samplers
sampler2D DiffuseSampler		: register(s0);
sampler2D AmbientSampler		: register(s1);
sampler2D OpacitySampler		: register(s2);

// Structs
struct VS_OUTPUT
{
    float4 position				: POSITION;
	float3 diffuse				: COLOR0;
	float3 specular				: COLOR1;
	float2 texCoordsDiffuse		: TEXCOORD0;
	float2 texCoordsAmbient		: TEXCOORD1;
	float2 texCoordsOpacity		: TEXCOORD2;
};

// Shaders
float4 main(VS_OUTPUT In) : COLOR
{
	// Base color
	float4 baseColor;
	float4 ambientColor;
	
	if (Booleans01.x != 0)
	{
		baseColor = tex2D(DiffuseSampler, In.texCoordsDiffuse);

		if (Booleans02.z)
		{
			clip(baseColor.a - 0.5f);
		}
		
		baseColor.rgb *= Levels.x;
	}
	else
		baseColor = float4(1, 1, 1, 1);

	if (Booleans01.y != 0)
		ambientColor = tex2D(AmbientSampler, In.texCoordsAmbient) * Levels.y;
	else
		ambientColor = float4(1, 1, 1, 1);

	// Alpha
	float alpha = DiffuseColor.a;

	if (Booleans02.x != 0)
		alpha *= tex2D(OpacitySampler, In.texCoordsOpacity).a;

	// Composition
	float3 finalDiffuse = saturate(In.diffuse + AmbientColor.rgb) * baseColor.rgb;

	return float4(finalDiffuse * ambientColor.rgb + In.specular, alpha);
}