float4x4 WorldViewProjection;
float4x4 World;	
float4x4 View;				
float4 LightInfo;				

float4 DiffuseColor;				
float4 SpecularColor;			
float4 EmissiveColor;			
float3 EyePosition;			

float4x4 DiffuseTextureMatrix;
float4x4 AmbientTextureMatrix;	
float4x4 OpacityTextureMatrix;	

float4 Booleans01;				// x = UseDiffuseTexture, y = UseAmbientTexture, z = DiffuseUseCanal2, w = AmbientUseCanal2
float4 Booleans02;				// x = UseOpacityTexture, y = OpacityUseCanal2, z = AlphaTestEnable

// Structs
struct VS_INPUT
{
    float4 position				: POSITION;
	float3 normal				: NORMAL;
	float2 texCoords01			: TEXCOORD0;
	float2 texCoords02			: TEXCOORD1;
};

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
VS_OUTPUT main(VS_INPUT In)
{
    VS_OUTPUT Out = (VS_OUTPUT)0;

    Out.position = mul(In.position, WorldViewProjection);

	float3 positionW = mul(In.position, World).xyz;
	float3 normalW = normalize(mul(In.normal, (float3x3)World));

	if (Booleans01.x != 0)
	{
		if (Booleans01.z != 0)
			Out.texCoordsDiffuse = mul(float3(In.texCoords02, 1.0f), (float3x3)DiffuseTextureMatrix).xy;
		else
			Out.texCoordsDiffuse = mul(float3(In.texCoords01, 1.0f), (float3x3)DiffuseTextureMatrix).xy;
	}
	else
		Out.texCoordsDiffuse = 0;

	if (Booleans01.y != 0)
	{
		if (Booleans01.w != 0)
			Out.texCoordsAmbient = mul(float3(In.texCoords02, 1.0f), (float3x3)AmbientTextureMatrix).xy;
		else
			Out.texCoordsAmbient = mul(float3(In.texCoords01, 1.0f), (float3x3)AmbientTextureMatrix).xy;
	}
	else
		Out.texCoordsAmbient = 0;

	if (Booleans02.x != 0)
	{
		if (Booleans02.y != 0)
			Out.texCoordsOpacity = mul(float3(In.texCoords02, 1.0f), (float3x3)OpacityTextureMatrix).xy;
		else
			Out.texCoordsOpacity = mul(float3(In.texCoords01, 1.0f), (float3x3)OpacityTextureMatrix).xy;
	}
	else
		Out.texCoordsOpacity = 0;

	// Light equation
	float3 lightData = LightInfo.xyz;
	float3 lightVectorW;
	float3 viewDirectionW = normalize(EyePosition - positionW);

	if (LightInfo.w != 0)
		lightVectorW = normalize(lightData - positionW);
	else
		lightVectorW = -normalize(lightData);
	
	// Diffuse
	float ndl = max(0, dot(normalW, lightVectorW));

	// Specular
	float3 floatAngleWS = normalize(viewDirectionW + lightVectorW);
	float specComp = max(0.000001f, dot(normalW, floatAngleWS));
	specComp = pow(specComp, SpecularColor.a);

	Out.diffuse = saturate(ndl * DiffuseColor.rgb + EmissiveColor.rgb);
	Out.specular = specComp * SpecularColor.rgb;

    return Out;
}
