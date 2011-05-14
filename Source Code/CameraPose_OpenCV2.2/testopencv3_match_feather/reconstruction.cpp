#include "reconstruction.h"

const int Case00 = 0;//case R0 and T0
const int Case01 = 1;//R0 T1
const int Case10 = 2;
const int Case11 = 3;

//Find max absolute of element in a matrix
float max_abs(CvMat *M)
{
	int step = M->step/sizeof(float);
	float max = 0;
	float temp = 0;
	for(int i=0;i<M->rows;i++)
		for(int j=0;j<M->cols;j++)
		{
			temp = fabs(M->data.fl[i*step+j]);
			if(temp>max) max= temp;
		}
	return max;
}

//Norm each row of matrix
CvMat *norm_rows(CvMat *M)
{
	CvMat *M2=cvCloneMat(M);
	int step = M->step/sizeof(float);
	float t=0;
	int i,j;
	float temp = 0;

	for(i=0;i<M->rows;i++)
	{
		temp = 0;
		for(j=0;j<M->cols;j++)
		{
			temp = temp + M->data.fl[i*step+j]*M->data.fl[i*step+j];
		}
		temp = sqrt(temp);
		for(j=0;j<M->cols;j++)
		{
			M2->data.fl[i*step+j] = M2->data.fl[i*step+j]/temp;
		}
	}

	return M2;
}


CvMat *h_convert(CvMat *point)
{

	int cols = point->cols;
	float temp;
	CvMat *h = cvCreateMat(3,cols,CV_32F);
	int step_h = h->step/sizeof(float);
	int step_point = point->step/sizeof(float);
	int j;
	for(j=0; j<cols; j++)
	{
		h->data.fl[0*step_h+j] = point->data.fl[0*step_point + j];
		h->data.fl[1*step_h+j] = point->data.fl[1*step_point + j];
		h->data.fl[2*step_h+j] = 1;
	}

	return h;
}

void computeRt(int co,CvMat*K, CvMat *F, CvMat **R1, CvMat **R2, CvMat **T1, CvMat **T2)
{
	//Compute essential matrix
	CvMat *E = cvCreateMat(3,3,CV_32F);
	cvTranspose(K,E);
	cvMatMul(E,F,E);
	cvMatMul(E,K,E);

	//Compute R and T
	CvMat* W= 	cvCreateMat(3,3,CV_32F);
	CvMat *U  = cvCreateMat(3,3,CV_32F);
	CvMat *D  = cvCreateMat(3,3,CV_32F);
	CvMat *Vt = cvCreateMat(3,3,CV_32F);

	//Clear old mat and create new mat
	/*cvReleaseMat(R1);
	cvReleaseMat(R2);
	cvReleaseMat(T1);
	cvReleaseMat(T2);*/

	*R1= cvCreateMat(3,3,CV_32F);
	*R2  = cvCreateMat(3,3,CV_32F);
	*T1  = cvCreateMat(3,1,CV_32F);
	*T2 = cvCreateMat(3,1,CV_32F);

	int step_U= U->step/sizeof(float);
	int step_T=(*T1)->step/sizeof(float);

	//W
	W->data.fl[0*step_U+0]=0;
	W->data.fl[1*step_U+0]=1;
	W->data.fl[2*step_U+0]=0;

	W->data.fl[0*step_U+1]=-1;
	W->data.fl[1*step_U+1]=0;
	W->data.fl[2*step_U+1]=0;

	W->data.fl[0*step_U+2]=0;
	W->data.fl[1*step_U+2]=0;
	W->data.fl[2*step_U+2]=1;


	cvSVD(E,D,U,Vt,CV_SVD_V_T );

	//Set following matlab
	Vt->data.fl[0*step_U+0] = co*Vt->data.fl[0*step_U+0];
	Vt->data.fl[0*step_U+1] = co*Vt->data.fl[0*step_U+1];
	Vt->data.fl[0*step_U+2] = co*Vt->data.fl[0*step_U+2];

	Vt->data.fl[1*step_U+0] = co*Vt->data.fl[1*step_U+0];
	Vt->data.fl[1*step_U+1] = co*Vt->data.fl[1*step_U+1];
	Vt->data.fl[1*step_U+2] = co*Vt->data.fl[1*step_U+2];

	Vt->data.fl[2*step_U+0] = co*Vt->data.fl[2*step_U+0];
	Vt->data.fl[2*step_U+1] = co*Vt->data.fl[2*step_U+1];
	Vt->data.fl[2*step_U+2] = co*Vt->data.fl[2*step_U+2];

	//**********************************************************
	 //R=UWVt or R=UWtVt
	 //t= u3 or t=-u3
	 //u3 is the third column of U


	//	Calculating rotation matrix R1
	cvMatMul(U,W,*R1);
	cvMatMul(*R1,Vt,*R1);	

	//	Calculating rotation matrix R2
	cvTranspose(W,*R2);
	cvMatMul(U,*R2,*R2);
	cvMatMul(*R2,Vt,*R2);

	//	Calculating vector t1
	(*T1)->data.fl[0*step_T] = U->data.fl[0*step_U+2];
	(*T1)->data.fl[1*step_T] = U->data.fl[1*step_U+2];
	(*T1)->data.fl[2*step_T] = U->data.fl[2*step_U+2];

	//	Calculating vector t2
	(*T2)->data.fl[0*step_T] = -U->data.fl[0*step_U+2];
	(*T2)->data.fl[1*step_T] =- U->data.fl[1*step_U+2];
	(*T2)->data.fl[2*step_T] = -U->data.fl[2*step_U+2];

	cvReleaseMat(&U);
	cvReleaseMat(&D);
	cvReleaseMat(&Vt);
	cvReleaseMat(&W);
}

CvMat *calc3D_SVD(int co,CvMat *K, CvMat*P0, CvMat *P1, CvMat *point1, CvMat *point2)
{
	CvMat *X = cvCreateMat(4,1,CV_32F);
	CvMat *x0 = h_convert(point1);
	CvMat *x1 = h_convert(point2);
	CvMat *K_inv = cvCreateMat(3,3,CV_32F);
	CvMat *A = cvCreateMat(4,4,CV_32F);
	int step_A = A->step/sizeof(float);
	int step_P = P1->step/sizeof(float);
	int step_x = x0->step/sizeof(float);
	int step_X = X->step/sizeof(float);

	cvInv(K,K_inv);
	cvMatMul(K_inv,x0,x0);
	cvMatMul(K_inv,x1,x1);

	//Building matrix A
	A->data.fl[step_A*0+0] = x0->data.fl[0*step_x] * P0->data.fl[2*step_P+0]-P0->data.fl[0*step_P+0];
	A->data.fl[step_A*0+1] = x0->data.fl[0*step_x] * P0->data.fl[2*step_P+1]-P0->data.fl[0*step_P+1];
	A->data.fl[step_A*0+2] = x0->data.fl[0*step_x] * P0->data.fl[2*step_P+2]-P0->data.fl[0*step_P+2];
	A->data.fl[step_A*0+3] = x0->data.fl[0*step_x] * P0->data.fl[2*step_P+3]-P0->data.fl[0*step_P+3];

	A->data.fl[step_A*1+0] = x0->data.fl[1*step_x] * P0->data.fl[2*step_P+0]-P0->data.fl[1*step_P+0];
	A->data.fl[step_A*1+1] = x0->data.fl[1*step_x] * P0->data.fl[2*step_P+1]-P0->data.fl[1*step_P+1];
	A->data.fl[step_A*1+2] = x0->data.fl[1*step_x] * P0->data.fl[2*step_P+2]-P0->data.fl[1*step_P+2];
	A->data.fl[step_A*1+3] = x0->data.fl[1*step_x] * P0->data.fl[2*step_P+3]-P0->data.fl[1*step_P+3];


	A->data.fl[step_A*2+0] = x1->data.fl[0*step_x] * P1->data.fl[2*step_P+0]-P1->data.fl[0*step_P+0];
	A->data.fl[step_A*2+1] = x1->data.fl[0*step_x] * P1->data.fl[2*step_P+1]-P1->data.fl[0*step_P+1];
	A->data.fl[step_A*2+2] = x1->data.fl[0*step_x] * P1->data.fl[2*step_P+2]-P1->data.fl[0*step_P+2];
	A->data.fl[step_A*2+3] = x1->data.fl[0*step_x] * P1->data.fl[2*step_P+3]-P1->data.fl[0*step_P+3];

	A->data.fl[step_A*3+0] = x1->data.fl[1*step_x] * P1->data.fl[2*step_P+0]-P1->data.fl[1*step_P+0];
	A->data.fl[step_A*3+1] = x1->data.fl[1*step_x] * P1->data.fl[2*step_P+1]-P1->data.fl[1*step_P+1];
	A->data.fl[step_A*3+2] = x1->data.fl[1*step_x] * P1->data.fl[2*step_P+2]-P1->data.fl[1*step_P+2];
	A->data.fl[step_A*3+3] = x1->data.fl[1*step_x] * P1->data.fl[2*step_P+3]-P1->data.fl[1*step_P+3];

	//Normalize matrix A
	CvMat *A_norm = norm_rows(A);

	//Calculate 3D coordinates
	CvMat *U  = cvCreateMat(4,4,CV_32F);
	CvMat *D  = cvCreateMat(4,4,CV_32F);
	CvMat *V = cvCreateMat(4,4,CV_32F);
	int step_V = V->step/sizeof(float);

	cvSVD(A_norm,D,U,V);

	//Set following matlab
	X->data.fl[0*step_X] = co*V->data.fl[0*step_V+3];
	X->data.fl[1*step_X] = co*V->data.fl[1*step_V+3];
	X->data.fl[2*step_X] = co*V->data.fl[2*step_V+3];
	X->data.fl[3*step_X] = co*V->data.fl[3*step_V+3];

	cvReleaseMat(&A);
	cvReleaseMat(&A_norm);
	cvReleaseMat(&U);
	cvReleaseMat(&D);
	cvReleaseMat(&V);
	cvReleaseMat(&x0);
	cvReleaseMat(&x1);
	cvReleaseMat(&K_inv);

	return X;
}

//Find projective matrix of second camera
CvMat *find_P1(CvMat *R, CvMat *T)
{
	CvMat *P1 = cvCreateMat(3,4,CV_32F);
	int step_P1 = P1->step/sizeof(float);
	int step_R = R->step/sizeof(float);
	int step_T = T->step/sizeof(float);

	// P1=[R|T]
	float max = max_abs(T);
	P1->data.fl[0*step_P1+0] = R->data.fl[0*step_R+0];
	P1->data.fl[1*step_P1+0] = R->data.fl[1*step_R+0];
	P1->data.fl[2*step_P1+0] = R->data.fl[2*step_R+0];

	P1->data.fl[0*step_P1+1] = R->data.fl[0*step_R+1];
	P1->data.fl[1*step_P1+1] = R->data.fl[1*step_R+1];
	P1->data.fl[2*step_P1+1] = R->data.fl[2*step_R+1];

	P1->data.fl[0*step_P1+2] = R->data.fl[0*step_R+2];
	P1->data.fl[1*step_P1+2] = R->data.fl[1*step_R+2];
	P1->data.fl[2*step_P1+2] = R->data.fl[2*step_R+2];

	P1->data.fl[0*step_P1+3] = (T->data.fl[0*step_T])/max;
	P1->data.fl[1*step_P1+3] = (T->data.fl[1*step_T])/max;
	P1->data.fl[2*step_P1+3] = (T->data.fl[2*step_T])/max;

	return P1;
}

//Find true R and T, return the case
int true_RT(int co,CvMat *K, CvMat *R0, CvMat *R1,CvMat *T0, CvMat *T1,float x0, float y0, float x1, float y1)
{
	bool stop = false;
	int true_case = Case00;
	CvMat *X = NULL;
	CvMat *P0 = cvCreateMat(3,4,CV_32F);
	CvMat *P1 = NULL;
	int step_P = (P0)->step/sizeof(float);

	CvMat *point1 = cvCreateMat(2,1,CV_32F);
	CvMat *point2 = cvCreateMat(2,1,CV_32F);
	int step_x = point1->step/sizeof(float);

	CvMat *temp = cvCreateMat(3,1,CV_32F);
	int step_temp = temp->step/sizeof(float);

	point1->data.fl[0*step_x] = x0;
	point1->data.fl[1*step_x] = y0;
	point2->data.fl[0*step_x] = x1;
	point2->data.fl[1*step_x] = y1;

	//Set real world coordinate is camera 1 principle point
	(P0)->data.fl[0*step_P+0] = 1;
	(P0)->data.fl[0*step_P+1] = 0;
	(P0)->data.fl[0*step_P+2] = 0;
	(P0)->data.fl[0*step_P+3] = 0;

	(P0)->data.fl[1*step_P+0] = 0;
	(P0)->data.fl[1*step_P+1] = 1;
	(P0)->data.fl[1*step_P+2] = 0;
	(P0)->data.fl[1*step_P+3] = 0;

	(P0)->data.fl[2*step_P+0] = 0;
	(P0)->data.fl[2*step_P+1] = 0;
	(P0)->data.fl[2*step_P+2] = 1;
	(P0)->data.fl[2*step_P+3] = 0;


	//Check to find true case
	float w,T,m3n,det,depth[2];
	int i,j,sign;
	int step_X;
	//Case00
	(P1) = find_P1(R0, T0);
	X = calc3D_SVD(co,K, P0, P1, point1, point2);
	step_X = X->step/sizeof(float);

	//Check depth of first camera
	cvMatMul(P0,X,temp);
	w = temp->data.fl[2*step_temp];
	T = X->data.fl[3*step_X];
	m3n = 0;
	for(i=0;i<3;i++)
	{
		m3n = m3n + (P0)->data.fl[2*step_P+i]*(P0)->data.fl[2*step_P+i];
	}
	m3n = sqrt (m3n);
	sign = 1;
	depth[0] = sign*w/(T*m3n);

	//Check depth of second camera
	cvMatMul(P1,X,temp);
	w = temp->data.fl[2*step_temp];
	T = X->data.fl[3*step_X];
	m3n = 0;
	for(i=0;i<3;i++)
	{
		m3n = m3n + P1->data.fl[2*step_P+i]*(P1)->data.fl[2*step_P+i];
	}
	m3n = sqrt (m3n);
	det = float(cvDet(R0));
	//if(det <0) sign = -1;
	//else sign = 1;
	depth[1] = sign*w/(T*m3n);

	//Check if case fit the model
	if(depth[0]>=0&&depth[1]>=0)
	{
		stop = true;
		true_case = Case00;
	}


	//Case 01
	if(stop == false)
	{
		cvReleaseMat(&P1);
		cvReleaseMat(&X);
		(P1) = find_P1(R0, T1);
		X = calc3D_SVD(co,K, P0, P1, point1, point2);
		step_X = X->step/sizeof(float);

		//Check depth of first camera
		cvMatMul(P0,X,temp);
		w = temp->data.fl[2*step_temp];
		T = X->data.fl[3*step_X];
		m3n = 0;
		for(i=0;i<3;i++)
		{
			m3n = m3n + (P0)->data.fl[2*step_P+i]*(P0)->data.fl[2*step_P+i];
		}
		m3n = sqrt (m3n);
		sign = 1;
		depth[0] = sign*w/(T*m3n);

		//Check depth of second camera
		cvMatMul(P1,X,temp);
		w = temp->data.fl[2*step_temp];
		T = X->data.fl[3*step_X];
		m3n = 0;
		for(i=0;i<3;i++)
		{
			m3n = m3n + (P1)->data.fl[2*step_P+i]*(P1)->data.fl[2*step_P+i];
		}
		m3n = sqrt (m3n);
		det = float(cvDet(R0));
		//if(det <0) sign = -1;
		//else sign = 1;
		depth[1] = sign*w/(T*m3n);

		//Check if case fit the model
		if(depth[0]>=0&&depth[1]>=0)
		{
			stop = true;
			true_case = Case01;
		}



	}

	//Case 10
	if(stop == false)
	{
		cvReleaseMat(&P1);
		cvReleaseMat(&X);
		(P1) = find_P1(R1, T0);
		X = calc3D_SVD(co,K, P0, P1, point1, point2);
		step_X = X->step/sizeof(float);

		//Check depth of first camera
		cvMatMul(P0,X,temp);
		w = temp->data.fl[2*step_temp];
		T = X->data.fl[3*step_X];
		m3n = 0;
		for(i=0;i<3;i++)
		{
			m3n = m3n + (P0)->data.fl[2*step_P+i]*(P0)->data.fl[2*step_P+i];
		}
		m3n = sqrt (m3n);
		sign = 1;
		depth[0] = sign*w/(T*m3n);

		//Check depth of second camera
		cvMatMul(P1,X,temp);
		w = temp->data.fl[2*step_temp];
		T = X->data.fl[3*step_X];
		m3n = 0;
		for(i=0;i<3;i++)
		{
			m3n = m3n + (P1)->data.fl[2*step_P+i]*(P1)->data.fl[2*step_P+i];
		}
		m3n = sqrt (m3n);
		det = float(cvDet(R1));
		//if(det <0) sign = -1;
		//else sign = 1;
		depth[1] = sign*w/(T*m3n);

		//Check if case fit the model
		if(depth[0]>=0&&depth[1]>=0)
		{
			stop = true;
			true_case = Case10;
		}
	}

	//Case 11
	if(stop == false)
	{
		cvReleaseMat(&P1);
		cvReleaseMat(&X);
		(P1) = find_P1(R1, T1);
		X = calc3D_SVD(co,K, P0, P1, point1, point2);
		step_X = X->step/sizeof(float);

		//Check depth of first camera
		cvMatMul(P0,X,temp);
		w = temp->data.fl[2*step_temp];
		T = X->data.fl[3*step_X];
		m3n = 0;
		for(i=0;i<3;i++)
		{
			m3n = m3n + (P0)->data.fl[2*step_P+i]*(P0)->data.fl[2*step_P+i];
		}
		m3n = sqrt (m3n);
		sign = 1;
		depth[0] = sign*w/(T*m3n);

		//Check depth of second camera
		cvMatMul(P1,X,temp);
		w = temp->data.fl[2*step_temp];
		T = X->data.fl[3*step_X];
		m3n = 0;
		for(i=0;i<3;i++)
		{
			m3n = m3n + (P1)->data.fl[2*step_P+i]*(P1)->data.fl[2*step_P+i];
		}
		m3n = sqrt (m3n);
		det = float(cvDet(R1));
		//if(det <0) sign = -1;
		//else sign = 1;
		depth[1] = sign*w/(T*m3n);

		//Check if case fit the model
		if(depth[0]>=0&&depth[1]>=0)
		{
			stop = true;
			true_case = Case11;
		}
	}
	cvReleaseMat(&P0);
	cvReleaseMat(&P1);
	cvReleaseMat(&point1);
	cvReleaseMat(&point2);
	cvReleaseMat(&temp);
	cvReleaseMat(&X);
	return true_case;
}

int best_case(int co,CvMat *K,CvMat *F, CvMat *points1, CvMat *points2,CvMat**R, CvMat **T, CvMat **P0, CvMat **P1)
{
	/*cvReleaseMat(R);
	cvReleaseMat(T);
	cvReleaseMat(P0);
	cvReleaseMat(P1);*/

	CvMat *R0 = NULL;
	CvMat *R1 = NULL;
	CvMat *T0 = NULL;
	CvMat *T1 = NULL;

	//Compute R and T
	computeRt(co, K, F, &R0, &R1, &T0, &T1);
	//co = myCompute(K, F, &R0, &R1, &T0, &T1);

	//Find the best solution for R,T and P
	int true_case = 0;
	int step_points = points1->step/sizeof(float);
	int i,j;
	int mark[4]={0,0,0,0};
	float x0,x1,y0,y1;
	for(i=0; i<points1->cols;i++)
	{
		x0 = points1->data.fl[0*step_points+i];
		y0 = points1->data.fl[1*step_points+i];
		x1 = points2->data.fl[0*step_points+i];
		y1 = points2->data.fl[1*step_points+i];

		true_case = true_RT(co,K,R0,R1,T0,T1,x0,y0,x1, y1);
		if(true_case == Case00) mark[0]++;
		if(true_case == Case01) mark[1]++;
		if(true_case == Case10) mark[2]++;
		if(true_case == Case11) mark[3]++;
	}
	int max=mark[3];
	if(mark[0]>= max) {max = mark[0]; true_case = Case00;}
	if(mark[1]>= max) {max = mark[1]; true_case = Case01;}
	if(mark[2]>= max) {max = mark[2]; true_case = Case10;}
	if(mark[3]>= max) {max = mark[3]; true_case = Case11;}

	if(true_case == Case00) {*R=R0;*T=T0;}
	if(true_case == Case01) {*R=R0;*T=T1;}
	if(true_case == Case10) {*R=R1;*T=T0;}
	if(true_case == Case11) {*R=R1;*T=T1;}

	//Return P0 and P1
	*P0 = cvCreateMat(3,4,CV_32F);
	int step_P = (*P0)->step/sizeof(float);
	//Set real world coordinate is camera 1 principle point
	(*P0)->data.fl[0*step_P+0] = 1;
	(*P0)->data.fl[0*step_P+1] = 0;
	(*P0)->data.fl[0*step_P+2] = 0;
	(*P0)->data.fl[0*step_P+3] = 0;

	(*P0)->data.fl[1*step_P+0] = 0;
	(*P0)->data.fl[1*step_P+1] = 1;
	(*P0)->data.fl[1*step_P+2] = 0;
	(*P0)->data.fl[1*step_P+3] = 0;

	(*P0)->data.fl[2*step_P+0] = 0;
	(*P0)->data.fl[2*step_P+1] = 0;
	(*P0)->data.fl[2*step_P+2] = 1;
	(*P0)->data.fl[2*step_P+3] = 0;

	*P1 = find_P1(*R, *T);
	printf("\nSupporting points for rotation matrix and translation vector: %d \n",max);


	return true_case;
}