/****************************************************************************
*                                                                           *
*  OpenNI 1.1 Alpha                                                         *
*  Copyright (C) 2011 PrimeSense Ltd.                                       *
*                                                                           *
*  This file is part of OpenNI.                                             *
*                                                                           *
*  OpenNI is free software: you can redistribute it and/or modify           *
*  it under the terms of the GNU Lesser General Public License as published *
*  by the Free Software Foundation, either version 3 of the License, or     *
*  (at your option) any later version.                                      *
*                                                                           *
*  OpenNI is distributed in the hope that it will be useful,                *
*  but WITHOUT ANY WARRANTY; without even the implied warranty of           *
*  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the             *
*  GNU Lesser General Public License for more details.                      *
*                                                                           *
*  You should have received a copy of the GNU Lesser General Public License *
*  along with OpenNI. If not, see <http://www.gnu.org/licenses/>.           *
*                                                                           *
****************************************************************************/
//---------------------------------------------------------------------------
// Includes
//---------------------------------------------------------------------------
#include <XnOS.h>
#if (XN_PLATFORM == XN_PLATFORM_MACOSX)
#include <GLUT/glut.h>
#else
#include <GL/glut.h>
#endif
#include <math.h>

#include <XnCppWrapper.h>
#include <iostream>
#include <fstream>
#include <string>
using namespace std;
using namespace xn;

//---------------------------------------------------------------------------
// Defines
//---------------------------------------------------------------------------
#define SAMPLE_XML_PATH "c:\\Program Files (x86)\\OpenNI\\Data\\SamplesConfig.xml"

#define GL_WIN_SIZE_X 1280
#define GL_WIN_SIZE_Y 1024

#define DISPLAY_MODE_OVERLAY	1
#define DISPLAY_MODE_DEPTH		2
#define DISPLAY_MODE_IMAGE		3
#define DEFAULT_DISPLAY_MODE	DISPLAY_MODE_OVERLAY

#define MAX_DEPTH 10000

//---------------------------------------------------------------------------
// Globals
//---------------------------------------------------------------------------
float g_pDepthHist[MAX_DEPTH];
XnRGB24Pixel* g_pTexMap = NULL;
unsigned int g_nTexMapX = 0;
unsigned int g_nTexMapY = 0;

unsigned int g_nViewState = DEFAULT_DISPLAY_MODE;

Context g_context;
DepthGenerator g_depth;
ImageGenerator g_image;
DepthMetaData g_depthMD;
ImageMetaData g_imageMD;

int g_iFrame = 0;


//---------------------------------------------------------------------------
// Code
//---------------------------------------------------------------------------
string str_itoa(int i, int digit)
{
	char c[20];
	itoa(i, c, 10);
	string strTemp = string(c);
	while (strTemp.length() < digit)
	{
		strTemp = "0" + strTemp;
	}
	return strTemp;
}

void glutIdle (void)
{
	// Display the frame
	glutPostRedisplay();
}

void glutDisplay (void)
{
	XnStatus rc = XN_STATUS_OK;

	// Read a new frame
//	rc = g_context.WaitAnyUpdateAll();
	rc = g_context.WaitAndUpdateAll();
	if (rc != XN_STATUS_OK)
	{
		printf("Read failed: %s\n", xnGetStatusString(rc));
		return;
	}

	g_depth.GetMetaData(g_depthMD);
	g_image.GetMetaData(g_imageMD);

	const XnDepthPixel* pDepth = g_depthMD.Data();
	const XnUInt8* pImage = g_imageMD.Data();

	unsigned int nImageScale = GL_WIN_SIZE_X / g_depthMD.FullXRes();

	// Copied from SimpleViewer
	// Clear the OpenGL buffers
	glClear (GL_COLOR_BUFFER_BIT | GL_DEPTH_BUFFER_BIT);

	// Setup the OpenGL viewpoint
	glMatrixMode(GL_PROJECTION);
	glPushMatrix();
	glLoadIdentity();
	glOrtho(0, GL_WIN_SIZE_X, GL_WIN_SIZE_Y, 0, -1.0, 1.0);

	// Calculate the accumulative histogram (the yellow display...)
	xnOSMemSet(g_pDepthHist, 0, MAX_DEPTH*sizeof(float));

	unsigned int nNumberOfPoints = 0;
	for (XnUInt y = 0; y < g_depthMD.YRes(); ++y)
	{
		for (XnUInt x = 0; x < g_depthMD.XRes(); ++x, ++pDepth)
		{
			if (*pDepth != 0)
			{
				g_pDepthHist[*pDepth]++;
				nNumberOfPoints++;
			}
		}
	}
	for (int nIndex=1; nIndex<MAX_DEPTH; nIndex++)
	{
		g_pDepthHist[nIndex] += g_pDepthHist[nIndex-1];
	}
	if (nNumberOfPoints)
	{
		for (int nIndex=1; nIndex<MAX_DEPTH; nIndex++)
		{
			g_pDepthHist[nIndex] = (unsigned int)(256 * (1.0f - (g_pDepthHist[nIndex] / nNumberOfPoints)));
		}
	}

	xnOSMemSet(g_pTexMap, 0, g_nTexMapX*g_nTexMapY*sizeof(XnRGB24Pixel));

	// check if we need to draw image frame to texture
	if (g_nViewState == DISPLAY_MODE_OVERLAY ||
		g_nViewState == DISPLAY_MODE_IMAGE)
	{
		const XnRGB24Pixel* pImageRow = g_imageMD.RGB24Data();
		XnRGB24Pixel* pTexRow = g_pTexMap + g_imageMD.YOffset() * g_nTexMapX;

		for (XnUInt y = 0; y < g_imageMD.YRes(); ++y)
		{
			const XnRGB24Pixel* pImage = pImageRow;// phan tu tiep theo trong anh
			XnRGB24Pixel* pTex = pTexRow + g_imageMD.XOffset();

			for (XnUInt x = 0; x < g_imageMD.XRes(); ++x, ++pImage, ++pTex)
			{
				*pTex = *pImage;
			}

			pImageRow += g_imageMD.XRes();
			pTexRow += g_nTexMapX;
		}
	}

	// check if we need to draw depth frame to texture

	//tao file tuong ung frame do, ko co depth -->0, nguoc lai ghi gia tri depth ra file
	//van de la can xacdinh depth co dung hay ko ?, can tru voi 1 khoang cach la bao nhieu de
	//ra depth that su??
	//string strFileName = "DepthFrame" + str_itoa(g_iFrame, 8) + ".txt";
	//ofstream ofs;
	//ofs.open(strFileName.c_str(), ios_base::out);

	//neu co depth thi ve depth de` len img
	if (g_nViewState == DISPLAY_MODE_OVERLAY ||
		g_nViewState == DISPLAY_MODE_DEPTH)
	{
		const XnDepthPixel* pDepthRow = g_depthMD.Data();
		XnRGB24Pixel* pTexRow = g_pTexMap + g_depthMD.YOffset() * g_nTexMapX;

		for (XnUInt y = 0; y < g_depthMD.YRes(); ++y)
		{
			const XnDepthPixel* pDepth = pDepthRow;
			XnRGB24Pixel* pTex = pTexRow + g_depthMD.XOffset();

			for (XnUInt x = 0; x < g_depthMD.XRes(); ++x, ++pDepth, ++pTex)
			{
				if (*pDepth != 0)
				{
					int nHistValue = g_pDepthHist[*pDepth];
					pTex->nRed = nHistValue;
					pTex->nGreen = nHistValue;
					pTex->nBlue = 0;

					//ofs<<*pDepth<<" ";
				}
				else
				{
					//ofs<<"0 ";
				}
			}
			//ofs<<endl;

			pDepthRow += g_depthMD.XRes();
			pTexRow += g_nTexMapX;
		}
	}

	//ofs.close();

	// Create the OpenGL texture map
	glTexParameteri(GL_TEXTURE_2D, GL_GENERATE_MIPMAP_SGIS, GL_TRUE);
	glTexParameteri(GL_TEXTURE_2D, GL_TEXTURE_MIN_FILTER, GL_LINEAR_MIPMAP_LINEAR);
	glTexParameteri(GL_TEXTURE_2D, GL_TEXTURE_MAG_FILTER, GL_LINEAR);
	glTexImage2D(GL_TEXTURE_2D, 0, GL_RGB, g_nTexMapX, g_nTexMapY, 0, GL_RGB, GL_UNSIGNED_BYTE, g_pTexMap);

	// Display the OpenGL texture map
	glColor4f(1,1,1,1);

	glBegin(GL_QUADS);

	int nXRes = g_depthMD.FullXRes();
	int nYRes = g_depthMD.FullYRes();

	// upper left
	glTexCoord2f(0, 0);
	glVertex2f(0, 0);
	// upper right
	glTexCoord2f((float)nXRes/(float)g_nTexMapX, 0);
	glVertex2f(GL_WIN_SIZE_X, 0);
	// bottom right
	glTexCoord2f((float)nXRes/(float)g_nTexMapX, (float)nYRes/(float)g_nTexMapY);
	glVertex2f(GL_WIN_SIZE_X, GL_WIN_SIZE_Y);
	// bottom left
	glTexCoord2f(0, (float)nYRes/(float)g_nTexMapY);
	glVertex2f(0, GL_WIN_SIZE_Y);

	glEnd();

	// Swap the OpenGL display buffers
	glutSwapBuffers();

	g_iFrame++;
}


        float degH = 57.0f;
        float degV = 43.0f;

        float radH;
        float radV;
        float dOH;

        void InitValues()
        {
            //radH = MathHelper.ToRadians(degH);
			radH = degH * 3.14 / 180.0f;
            //radV = MathHelper.ToRadians(degV);
			radV = degV * 3.14 / 180.0f;
			dOH = (float)(320.0f / tanf(radH / 2)); 
        }
        

struct Vector3
{
	int X;
	int Y;
	int Z;
};

        Vector3 Calc3DPos(Vector3 input)
        {
            Vector3 val;
            val.Z = -input.Z;
            val.X = input.Z * (input.X) / dOH;
            val.Y = -input.Z * (input.Y) / dOH;
            return val;
        }

//for case 2
void glutDisplay2 (void)
{
	XnStatus rc = XN_STATUS_OK;

	// Read a new frame
	rc = g_context.WaitAnyUpdateAll();
	if (rc != XN_STATUS_OK)
	{
		printf("Read failed: %s\n", xnGetStatusString(rc));
		return;
	}

	g_depth.GetMetaData(g_depthMD);
	g_image.GetMetaData(g_imageMD);

	if (g_imageMD.PixelFormat() != XN_PIXEL_FORMAT_RGB24)
			{
				printf("The device image format must be RGB24\n");
				return;
			}

	//const XnDepthPixel* pDepth = g_depthMD.Data();
	//const XnUInt8* pImage = g_imageMD.Data();

	//unsigned int nImageScale = GL_WIN_SIZE_X / g_depthMD.FullXRes();

	// Copied from SimpleViewer
	// Clear the OpenGL buffers
	//glClear (GL_COLOR_BUFFER_BIT | GL_DEPTH_BUFFER_BIT);

	//// Setup the OpenGL viewpoint
	//glMatrixMode(GL_PROJECTION);
	//glPushMatrix();
	//glLoadIdentity();
	//glOrtho(0, GL_WIN_SIZE_X, GL_WIN_SIZE_Y, 0, -1.0, 1.0);

	//xnOSMemSet(g_pTexMap, 0, g_nTexMapX*g_nTexMapY*sizeof(XnRGB24Pixel));

	string strFileName = "DepthFrame" + str_itoa(g_iFrame, 8) + ".txt";
	ofstream ofs;
	ofs.open(strFileName.c_str(), ios_base::out);

		const XnDepthPixel* pDepthRow = g_depthMD.Data();
		const XnRGB24Pixel* pImageRow = g_imageMD.RGB24Data();

		for (XnUInt y = 0; y < g_depthMD.YRes(); ++y)
		{
			const XnDepthPixel* pDepth = pDepthRow;
			const XnRGB24Pixel* pImage = pImageRow; 

			for (XnUInt x = 0; x < g_depthMD.XRes(); ++x, ++pDepth, ++pImage)
			{
				if (*pDepth != 0)
				{
					Vector3 v3Pos;
					v3Pos.Z = (*pDepth);
					v3Pos.X = (int)x - 320;
					v3Pos.Y = (int)y - 240;

					Vector3 v33DPos = Calc3DPos(v3Pos);

					unsigned int asd = (unsigned int)(pImage->nRed);
					ofs<<v33DPos.X<<" "<<v33DPos.Y<<" "<<v33DPos.Z<<" ";
					ofs<<(unsigned int)(pImage->nRed)<<" "<<(unsigned int)(pImage->nGreen)<<" "<<(unsigned int)(pImage->nBlue)<<endl;
				}
				else
				{
					ofs<<"0 0 0 ";
					ofs<<(unsigned int)(pImage->nRed)<<" "<<(unsigned int)(pImage->nGreen)<<" "<<(unsigned int)(pImage->nBlue)<<endl;
				}
			}

			pDepthRow += g_depthMD.XRes();
			pImageRow += g_imageMD.XRes();
		}

	ofs.close();
	cout<<"Done: "<<strFileName<<endl;

	//// Create the OpenGL texture map
	//glTexParameteri(GL_TEXTURE_2D, GL_GENERATE_MIPMAP_SGIS, GL_TRUE);
	//glTexParameteri(GL_TEXTURE_2D, GL_TEXTURE_MIN_FILTER, GL_LINEAR_MIPMAP_LINEAR);
	//glTexParameteri(GL_TEXTURE_2D, GL_TEXTURE_MAG_FILTER, GL_LINEAR);
	//glTexImage2D(GL_TEXTURE_2D, 0, GL_RGB, g_nTexMapX, g_nTexMapY, 0, GL_RGB, GL_UNSIGNED_BYTE, g_pTexMap);

	//// Display the OpenGL texture map
	//glColor4f(1,1,1,1);

	//glBegin(GL_QUADS);

	//int nXRes = g_depthMD.FullXRes();
	//int nYRes = g_depthMD.FullYRes();

	//// upper left
	//glTexCoord2f(0, 0);
	//glVertex2f(0, 0);
	//// upper right
	//glTexCoord2f((float)nXRes/(float)g_nTexMapX, 0);
	//glVertex2f(GL_WIN_SIZE_X, 0);
	//// bottom right
	//glTexCoord2f((float)nXRes/(float)g_nTexMapX, (float)nYRes/(float)g_nTexMapY);
	//glVertex2f(GL_WIN_SIZE_X, GL_WIN_SIZE_Y);
	//// bottom left
	//glTexCoord2f(0, (float)nYRes/(float)g_nTexMapY);
	//glVertex2f(0, GL_WIN_SIZE_Y);

	//glEnd();

	//// Swap the OpenGL display buffers
	//glutSwapBuffers();

	g_iFrame++;
}

void glutKeyboard (unsigned char key, int x, int y)
{
	switch (key)
	{
	case 27:
		exit (1);
	case '1':
		g_nViewState = DISPLAY_MODE_OVERLAY;
		g_depth.GetAlternativeViewPointCap().SetViewPoint(g_image);
		break;
	case '2':
		g_nViewState = DISPLAY_MODE_DEPTH;
		g_depth.GetAlternativeViewPointCap().ResetViewPoint();
		break;
	case '3':
		g_nViewState = DISPLAY_MODE_IMAGE;
		g_depth.GetAlternativeViewPointCap().ResetViewPoint();
		break;
	case 'm':
		g_context.SetGlobalMirror(!g_context.GetGlobalMirror());
		break;
	}
}


//capture file oni

int main(int argc, char* argv[])
{
	int a = 0;
	cin>>a;
	switch(a)
	{
	case 0:
		{
			XnStatus nRetVal;
			//Context context;
			EnumerationErrors errors;
			//capture to .oni file

			nRetVal = g_context.InitFromXmlFile(SAMPLE_XML_PATH, &errors);
			if (nRetVal == XN_STATUS_NO_NODE_PRESENT)
			{
				XnChar strError[1024];
				errors.ToString(strError, 1024);
				printf("%s\n", strError);
				return (nRetVal);
			}
			else if (nRetVal != XN_STATUS_OK)
			{
				printf("Open failed: %s\n", xnGetStatusString(nRetVal));
				return (nRetVal);
			}
			// Create a depth generator 
			//DepthGenerator depth; 
			nRetVal = g_depth.Create(g_context); 
			if (nRetVal != XN_STATUS_OK)
			{
				cout<<"err: nRetVal = depth.Create(g_context); ";
				return 1;
			}

			//ImageGenerator image;
			nRetVal = g_image.Create(g_context); 

			if (nRetVal != XN_STATUS_OK)
			{
				cout<<"err: nRetVal = image.Create(g_context); ";
				return 1;
			}

			//nRetVal = g_context.FindExistingNode(XN_NODE_TYPE_DEPTH, g_depth);
			//nRetVal = g_context.FindExistingNode(XN_NODE_TYPE_IMAGE, g_image);



			// Start generating 
			nRetVal = g_context.StartGeneratingAll(); 
			// TODO: check error code 
			if (nRetVal != XN_STATUS_OK)
			{
				cout<<"err: nRetVal = g_context.StartGeneratingAll(); ";
				return 1;
			}

			// Create Recorder 
			Recorder recorder; 

			nRetVal = recorder.Create(g_context); 
			// TODO: check error code 
			if (nRetVal != XN_STATUS_OK)
			{
				cout<<"err: nRetVal = recorder.Create(g_context); ";
				return 1;
			}

			// Init it 
			nRetVal = recorder.SetDestination(XN_RECORD_MEDIUM_FILE, 
				"d:\\asd2.oni"); 
			// TODO: check error code 
			if (nRetVal != XN_STATUS_OK)
			{
				cout<<"err: nRetVal = recorder.SetDestination(XN_RECORD_MEDIUM_FILE, ";
				return 1;
			}

			// Add depth node to recording 
			nRetVal = recorder.AddNodeToRecording(g_depth, XN_CODEC_16Z_EMB_TABLES); 
			// TODO: check error code 
			if (nRetVal != XN_STATUS_OK)
			{
				cout<<"err: nRetVal = recorder.AddNodeToRecording(g_depth, XN_CODEC_16Z_EMB_TABLES); ";
				return 1;
			}

			// Add depth node to recording 
			nRetVal = recorder.AddNodeToRecording(g_image, XN_CODEC_JPEG); 
			// TODO: check error code 
			if (nRetVal != XN_STATUS_OK)
			{
				cout<<"err: nRetVal = recorder.AddNodeToRecording(g_image, XN_CODEC_JPEG);  ";
				return 1;
			}
glutKeyboard('1', 0, 0);
			//g_context.WaitAndUpdateAll();
			g_depth.GetMetaData(g_depthMD);
			g_image.GetMetaData(g_imageMD);

			// Hybrid mode isn't supported in this sample
			if (g_imageMD.FullXRes() != g_depthMD.FullXRes() || g_imageMD.FullYRes() != g_depthMD.FullYRes())
			{
				printf ("The device depth and image resolution must be equal!\n");
				return 1;
			}

			// RGB is the only image format supported.
			if (g_imageMD.PixelFormat() != XN_PIXEL_FORMAT_RGB24)
			{
				printf("The device image format must be RGB24\n");
				return 1;
			}

			// Texture map init
			//??
			g_nTexMapX = (((unsigned short)(g_depthMD.FullXRes()-1) / 512) + 1) * 512;
			g_nTexMapY = (((unsigned short)(g_depthMD.FullYRes()-1) / 512) + 1) * 512;
			g_pTexMap = (XnRGB24Pixel*)malloc(g_nTexMapX * g_nTexMapY * sizeof(XnRGB24Pixel));

			// OpenGL init
			glutInit(&argc, argv);
			glutInitDisplayMode(GLUT_RGB | GLUT_DOUBLE | GLUT_DEPTH);
			glutInitWindowSize(GL_WIN_SIZE_X, GL_WIN_SIZE_Y);
			glutCreateWindow ("OpenNI Simple Viewer");
			glutFullScreen();
			glutSetCursor(GLUT_CURSOR_NONE);

			glutKeyboardFunc(glutKeyboard);
			glutDisplayFunc(glutDisplay);
			glutIdleFunc(glutIdle);

			glDisable(GL_DEPTH_TEST);
			glEnable(GL_TEXTURE_2D);

			
			// Per frame code is in glutDisplay
			glutMainLoop();
			break;
		}
	case 1:
		{

			XnStatus rc;

			EnumerationErrors errors;
			/*rc = g_context.InitFromXmlFile(SAMPLE_XML_PATH, &errors);
			if (rc == XN_STATUS_NO_NODE_PRESENT)
			{
			XnChar strError[1024];
			errors.ToString(strError, 1024);
			printf("%s\n", strError);
			return (rc);
			}
			else if (rc != XN_STATUS_OK)
			{
			printf("Open failed: %s\n", xnGetStatusString(rc));
			return (rc);
			}*/

			rc = g_context.Init(); 
			rc = g_context.OpenFileRecording("d:\\asd2.oni"); 
			rc = g_context.FindExistingNode(XN_NODE_TYPE_DEPTH, g_depth);
			rc = g_context.FindExistingNode(XN_NODE_TYPE_IMAGE, g_image);

			g_depth.GetMetaData(g_depthMD);
			g_image.GetMetaData(g_imageMD);

			// Hybrid mode isn't supported in this sample
			if (g_imageMD.FullXRes() != g_depthMD.FullXRes() || g_imageMD.FullYRes() != g_depthMD.FullYRes())
			{
				printf ("The device depth and image resolution must be equal!\n");
				return 1;
			}

			// RGB is the only image format supported.
			if (g_imageMD.PixelFormat() != XN_PIXEL_FORMAT_RGB24)
			{
				printf("The device image format must be RGB24\n");
				return 1;
			}

			// Texture map init
			//??
			g_nTexMapX = (((unsigned short)(g_depthMD.FullXRes()-1) / 512) + 1) * 512;
			g_nTexMapY = (((unsigned short)(g_depthMD.FullYRes()-1) / 512) + 1) * 512;
			g_pTexMap = (XnRGB24Pixel*)malloc(g_nTexMapX * g_nTexMapY * sizeof(XnRGB24Pixel));

			// OpenGL init
			glutInit(&argc, argv);
			glutInitDisplayMode(GLUT_RGB | GLUT_DOUBLE | GLUT_DEPTH);
			glutInitWindowSize(GL_WIN_SIZE_X, GL_WIN_SIZE_Y);
			glutCreateWindow ("OpenNI Simple Viewer");
			glutFullScreen();
			glutSetCursor(GLUT_CURSOR_NONE);

			glutKeyboardFunc(glutKeyboard);
			glutDisplayFunc(glutDisplay);
			glutIdleFunc(glutIdle);

			glDisable(GL_DEPTH_TEST);
			glEnable(GL_TEXTURE_2D);

			// Per frame code is in glutDisplay
			glutMainLoop();
		}
	case 2:
		{
			InitValues();
			g_iFrame = 0;

			XnStatus rc;

			rc = g_context.Init(); 
			rc = g_context.OpenFileRecording("d:\\asd2.oni"); 
			rc = g_context.FindExistingNode(XN_NODE_TYPE_DEPTH, g_depth);
			rc = g_context.FindExistingNode(XN_NODE_TYPE_IMAGE, g_image);

			//g_context.WaitAnyUpdateAll();

			while(true)
			{
				// Read a new frame
				rc = g_context.WaitAndUpdateAll();
				if (rc != XN_STATUS_OK)
				{
					printf("Read failed: %s\n", xnGetStatusString(rc));
					return 1;
				}

				g_depth.GetMetaData(g_depthMD);
				g_image.GetMetaData(g_imageMD);

				if (g_imageMD.PixelFormat() != XN_PIXEL_FORMAT_RGB24)
				{
					printf("The device image format must be RGB24\n");
					return 1;
				}

				string strFileName = "DepthFrame" + str_itoa(g_iFrame, 8) + ".txt";
				ofstream ofs;
				ofs.open(strFileName.c_str(), ios_base::out);

				const XnDepthPixel* pDepthRow = g_depthMD.Data();
				const XnRGB24Pixel* pImageRow = g_imageMD.RGB24Data();

				for (XnUInt y = 0; y < g_depthMD.YRes(); ++y)
				{
					const XnDepthPixel* pDepth = pDepthRow;
					const XnRGB24Pixel* pImage = pImageRow; 

					for (XnUInt x = 0; x < g_depthMD.XRes(); ++x, ++pDepth, ++pImage)
					{
						if (*pDepth != 0)
						{
							Vector3 v3Pos;
							v3Pos.Z = (*pDepth);
							v3Pos.X = (int)x - 320;
							v3Pos.Y = (int)y - 240;

							Vector3 v33DPos = Calc3DPos(v3Pos);

							unsigned int asd = (unsigned int)(pImage->nRed);
							ofs<<v33DPos.X<<" "<<v33DPos.Y<<" "<<v33DPos.Z<<" ";
							ofs<<(unsigned int)(pImage->nRed)<<" "<<(unsigned int)(pImage->nGreen)<<" "<<(unsigned int)(pImage->nBlue)<<endl;
						}
						else
						{
							ofs<<"0 0 0 ";
							ofs<<(unsigned int)(pImage->nRed)<<" "<<(unsigned int)(pImage->nGreen)<<" "<<(unsigned int)(pImage->nBlue)<<endl;
						}
					}

					pDepthRow += g_depthMD.XRes();
					pImageRow += g_imageMD.XRes();
				}

				ofs.close();
				cout<<"Done: "<<strFileName<<endl;

				g_iFrame++;
			}
		}
	default:
		{
		}
	}

	return 0;
}
