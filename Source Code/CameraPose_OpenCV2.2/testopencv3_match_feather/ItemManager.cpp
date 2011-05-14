#include "ItemManager.h"

ItemManager* ItemManager::CreateItemManager(int n, vector<string> filenames, int root)
{
	if(n < 0)
		return NULL;
	
	ItemManager* pItemManager = new ItemManager();
	pItemManager->nItems = n;
	pItemManager->pItems = new Item [pItemManager->nItems];	
	pItemManager->pIsConnected = new bool [pItemManager->nItems];
	for(int i = 0; i < pItemManager->nItems; i++)
	{
		pItemManager->pItems[i].SetFileName(filenames[i]);
		pItemManager->pIsConnected[i] = false;
	}

	pItemManager->pIsTried = new bool* [pItemManager->nItems];
	for(int i = 0; i < pItemManager->nItems; i++)
	{
		pItemManager->pIsTried[i] = new bool [pItemManager->nItems];
		for(int j = 0; j < pItemManager->nItems; j++)
		{
			pItemManager->pIsTried[i][j] = false;
		}
	}
	pItemManager->root = root;
	return pItemManager;
}

ItemManager::ItemManager()
{
	root = 0;
	nItems = 0;
	pItems = NULL;
	pIsConnected = NULL;

	K = cvCreateMat(3, 3, CV_32FC1);
	CV_MAT_ELEM(*K, float,  0, 0) = 1029.72334;
	CV_MAT_ELEM(*K, float,  0, 1) = 0;
	CV_MAT_ELEM(*K, float,  0, 2) = 311.96432;
	CV_MAT_ELEM(*K, float,  1, 0) = 0;
	CV_MAT_ELEM(*K, float,  1, 1) = 1031.58824;
	CV_MAT_ELEM(*K, float,  1, 2) = 288.66494;
	CV_MAT_ELEM(*K, float,  2, 0) = 0;
	CV_MAT_ELEM(*K, float,  2, 1) = 0;
	CV_MAT_ELEM(*K, float,  2, 2) = 1;
	/*
	CV_MAT_ELEM(*K, float,  0, 0) = 1.62914868e+003;
	CV_MAT_ELEM(*K, float,  0, 1) = 0;
	CV_MAT_ELEM(*K, float,  0, 2) = 8.18221680e+002;
	CV_MAT_ELEM(*K, float,  1, 0) = 0;
	CV_MAT_ELEM(*K, float,  1, 1) = 1.63047998e+003;
	CV_MAT_ELEM(*K, float,  1, 2) = 6.06374512e+002;
	CV_MAT_ELEM(*K, float,  2, 0) = 0;
	CV_MAT_ELEM(*K, float,  2, 1) = 0;
	CV_MAT_ELEM(*K, float,  2, 2) = 1;
	*/
	D = cvCreateMat(5, 1, CV_32FC1);
	CV_MAT_ELEM(*D, float,  0, 0) = 0.22127;
	CV_MAT_ELEM(*D, float,  1, 0) = 0.52348;
	CV_MAT_ELEM(*D, float,  2, 0) = -0.00138;
	CV_MAT_ELEM(*D, float,  3, 0) = -0.00342;
	CV_MAT_ELEM(*D, float,  4, 0) = 0;
}

ItemManager::~ItemManager(void)
{
	nItems = 0;
	delete[] pItems;
	delete[] pIsConnected;
	cvReleaseMat(&K);
	cvReleaseMat(&D);
}

void ItemManager::Print(ostream &out)
{
	for(int i = 0; i < nItems; i++)
		pItems[i].Print(out);
}

bool ItemManager::IsConnected(int index)
{
	return pIsConnected[index];
}

bool ItemManager::IsConnectable(int item1, int item2)
{
	if(0 < item1 && item1 < nItems)
		if(0 < item2 && item2 < nItems)
			return pItems[item1].IsConnectable(&pItems[item2]);
	return false;
}

bool ItemManager::IsTried(int item1, int item2)
{
	if(pIsTried[item1][item2] == true || pIsTried[item2][item1] == true)
		return true;
	return false;
}

int ItemManager::GetNextTarget()
{
	for(int i = 0; i < nItems; i++)
	{
		if(pIsConnected[i] == false)
		{
			for(int j = 0; j < nItems; j++)
			{
				if(pIsConnected[j])
					if(!IsTried(i, j) == false)
						return i;
			}
		}
	}
	return -1;
}

void ItemManager::InitFeatures()
{
	for(int i = 0; i < nItems; i++)
	{
		pItems[i].InitFeatures();
	}
}

void ItemManager::BuildTree()
{
	int target = root;
	pIsConnected[root] = true;
	for(int i = 0; i < nItems; i++)
	{
		if(i == root)
			continue;
		bool bConnected = pItems[root].Connect(&pItems[i], K, D);
		if(bConnected)
		{
			pIsConnected[i] = true;
		}
	}

	while((target = GetNextTarget()) != -1)
	{
		for(int i = 0; i < nItems; i++)
		{
			if(pIsConnected[i])
			{
				bool bConnected = pItems[target].Connect(&pItems[i], K, D);
				pIsTried[target][i] = true;
				if(bConnected)
				{
					pIsConnected[target] = true;
					break;
				}
			}
		}
	}	
}
