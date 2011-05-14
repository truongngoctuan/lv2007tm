#include "RotationMatrixUlti.h"


RotationMatrixUlti::RotationMatrixUlti(void)
{
}


RotationMatrixUlti::~RotationMatrixUlti(void)
{
}

//angle (độ) --> rotation matrix3x3
void RotationMatrixUlti::CreateRotationMatrixFromAngle( float AngleX, float AngleY, float AngleZ, CvMat *dest)
{
	//rotation matrix x = ψ; y = θ; z = φ;
	//cos θcos φ		sin ψ sin θ cos φ − cos ψ sin φ			cos ψ sin θ cos φ + sin ψ sin φ
	//cos θ sin φ		sin ψ sin θ sin φ + cos ψ cos φ			cos ψ sin θ sin φ − sin ψ cos φ
	//−sin θ			sin ψ cos θ								cos ψ cos θ

	float aX = ConvertToRadian(AngleX);
	float aY = ConvertToRadian(AngleY);
	float aZ = ConvertToRadian(AngleZ);

	CV_MAT_ELEM( *dest, float,  0, 0) = cos(aY) * cos (aZ);
	CV_MAT_ELEM( *dest, float,  0, 1) = sin(aX) * sin (aY) * cos(aZ) - cos(aX) * sin(aZ);
	CV_MAT_ELEM( *dest, float,  0, 2) = cos(aX) * sin (aY) * cos(aZ) + sin(aX) * sin(aZ);

	CV_MAT_ELEM( *dest, float, 1, 0) = cos(aY) * sin (aZ);
	CV_MAT_ELEM( *dest, float,  1, 1) = sin(aX) * sin (aY) * sin(aZ) + cos(aX) * cos(aZ);
	CV_MAT_ELEM( *dest, float,  1, 2) = cos(aX) * sin (aY) * sin(aZ) - sin(aX) * cos(aZ);

	CV_MAT_ELEM( *dest, float, 2, 0) = -sin(aY);
	CV_MAT_ELEM( *dest, float,  2, 1) = sin(aX) * cos (aY);
	CV_MAT_ELEM( *dest, float,  2, 2) = cos(aX) * cos (aY);
}

//rotation matrix3x3 --> angle (độ)
bool GanBang(float src, float dest, float SaiSoChoPhep)
{
	if (dest - SaiSoChoPhep <= src && src <= dest + SaiSoChoPhep)
	{
		return true;
	}
	return false;
}
void RotationMatrixUlti::CaculateAngleFromRotationMatrix(const CvMat *M, float &AngleX, float &AngleY, float &AngleZ)
{
	if (!GanBang(CV_MAT_ELEM( *M, float,  2, 0), -1, 0.1) && 
		!GanBang(CV_MAT_ELEM( *M, float,  2, 0), 1, 0.1))
	//if (M.at<float>(2,0) != -1 && 
	//	M.at<float>(2,0) != 1)
	//if (M.at<float>(2,0) != 0)
	{//rotation matrix x = ψ; y = θ; z = φ;
		float AngleY1 = - asinf(CV_MAT_ELEM( *M, float,  2, 0));
		float AngleX1 = atan2(CV_MAT_ELEM( *M, float,  2, 1) / cos(AngleY1), CV_MAT_ELEM( *M, float,  2, 2) / cos(AngleY1));
		float AngleZ1 = atan2(CV_MAT_ELEM( *M, float,  1, 0) / cos(AngleY1), CV_MAT_ELEM( *M, float,  0, 0) / cos(AngleY1));
		AngleX1 = AngleX1 / 3.14 * 180.0;
		AngleY1 = AngleY1 / 3.14 * 180.0;
		AngleZ1 = AngleZ1 / 3.14 * 180.0;

		//gán giá trị
		AngleX = AngleX1;
		AngleY = AngleY1;
		AngleZ = AngleZ1;
		//cout<<AngleX1<<" "<<AngleY1<< " "<<AngleZ1<<endl;

		float AngleY2 = 3.14 + asinf(CV_MAT_ELEM( *M, float,  2, 0));
		float AngleX2 = atan2(CV_MAT_ELEM( *M, float,  2, 1) / cos(AngleY2), CV_MAT_ELEM( *M, float,  2, 2) / cos(AngleY2));
		float AngleZ2 = atan2(CV_MAT_ELEM( *M, float,  1, 0) / cos(AngleY2), CV_MAT_ELEM( *M, float,  0, 0) / cos(AngleY2));
		AngleX2 = AngleX2 / 3.14 * 180.0;
		AngleY2 = AngleY2 / 3.14 * 180.0;
		AngleZ2 = AngleZ2 / 3.14 * 180.0;

		//cout<<AngleX2<<" "<<AngleY2<< " "<<AngleZ2<<endl;
	}
	else
	{
		/*φ = anything; can set to 0
		if (R31 = −1)
		θ = π/2
		ψ = φ + atan2(R12,R13)
		else
		θ = −π/2
		ψ = −φ + atan2(−R12,−R13)
		end if
		end if*/
		float AngleZ1 = 0;
		float AngleX1, AngleY1;

		if (GanBang(CV_MAT_ELEM( *M, float,  2, 0), -1, 0.1))
		{
			AngleY1 = 3.14 / 2;
			AngleX1 = 0 + atan2(CV_MAT_ELEM( *M, float,  0, 1), CV_MAT_ELEM( *M, float,  0, 2));
		}
		else
		{
			AngleY1 = - 3.14 / 2;
			AngleX1 = 0 + atan2(- CV_MAT_ELEM( *M, float,  0, 1), - CV_MAT_ELEM( *M, float,  0, 2));
		}

		//cout<<AngleX1<<" "<<AngleY1<< " "<<AngleZ1<<endl;

		AngleX = AngleX1;
		AngleY = AngleY1;
		AngleZ = AngleZ1;
	}
}

//util
float RotationMatrixUlti::ConvertToRadian(float fAngle)
{
	return fAngle * 3.14 / 180.0;
}
float RotationMatrixUlti::ConvertTo360(float fAngle)
{
	return fAngle / 3.14 * 180.0;
}