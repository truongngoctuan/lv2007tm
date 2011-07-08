float4 LightInfo;				

float4 AmbientColor;
float4 DiffuseColor;			
float4 SpecularColor;			
float4 EmissiveColor;			
float3 EyePosition;			

float4 Booleans01;					// x = UseDiffuseTexture, y = UseAmbientTexture, z = DiffuseUseCanal2, w = AmbientUseCanal2
float4 Booleans02;					// x = UseOpacityTexture, y = OpacityUseCanal2, z = AlphaTestEnable

float4 Levels;						// x = DiffuseLevel, y = AmbientLevel

// Samplers
sampler2D DiffuseSampler		: register(s0);
sampler2D AmbientSampler		: register(s1);
sampler2D OpacitySampler		: register(s2);

// Structs
struct VS_OUTPUT
{
    float4 position				: POSITION;
	float3 positionW			: TEXCOORD0;
	float3 normalW				: TEXCOORD1;
	float2 texCoordsDiffuse		: TEXCOORD2;
	float2 texCoordsAmbient		: TEXCOORD3;
	float2 texCoordsOpacity		: TEXCOORD4;
};


// Shaders
float4 main(VS_OUTPUT In) : COLOR
{
	float3 normalW = In.normalW;
	float3 lightData = LightInfo.xyz;
	float3 lightVectorW;
	float3 viewDirectionW = normalize(EyePosition - In.positionW);

	if (LightInfo.w != 0)
		lightVectorW = normalize(lightData - In.positionW);
	else
		lightVectorW = -normalize(lightData);

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

	// Diffuse
	float ndl = max(0, dot(normalW, lightVectorW));

	// Specular
	float3 floatAngleWS = normalize(viewDirectionW + lightVectorW);
	float specComp = max(0.000001f, dot(normalW, floatAngleWS));
	specComp = pow(specComp, SpecularColor.a);

	// Alpha
	float alpha = DiffuseColor.a;

	if (Booleans02.x != 0)
		alpha *= tex2D(OpacitySampler, In.texCoordsOpacity).a;

	// Composition
	float3 finalDiffuse = saturate(ndl * DiffuseColor.rgb +  EmissiveColor.rgb);
	finalDiffuse = saturate(finalDiffuse + AmbientColor.rgb) * baseColor.rgb;
	float3 finalSpecular = specComp * SpecularColor.rgb;

	return float4(finalDiffuse * ambientColor.rgb + finalSpecular, alpha);
}