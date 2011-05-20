#include "TestIsConnectable.h"

void TestItemConnectable(ItemManager* pItemManager, int iItem1, int iItem2, bool bIsTrue)
{
	if (bIsTrue)
	{
		ASSERT((pItemManager->GetItem(iItem1)->GetFileName() + " - " + pItemManager->GetItem(iItem2)->GetFileName()).c_str(), 
			(pItemManager->IsConnectable(iItem1, iItem2)));
	}
	else
	{
		ASSERT((pItemManager->GetItem(iItem1)->GetFileName() + " - " + pItemManager->GetItem(iItem2)->GetFileName()).c_str(), 
			!(pItemManager->IsConnectable(iItem1, iItem2)));
	}
}

void TestIsConnectable1x()
{
	vector<string> arrFileName;

	FILE *fptr = fopen("test\\TestIsconnectable1x.txt","r");
	char names[2048];

	while(fscanf(fptr,"%s ",names)==1)
	{
		arrFileName.push_back(names);
	}

	ItemManager* pItemManager = ItemManager::CreateItemManager(arrFileName.size(), arrFileName);
	pItemManager->InitFeatures();

	TestItemConnectable(pItemManager, 0, 0, true);
	TestItemConnectable(pItemManager, 0, 1, true);
	TestItemConnectable(pItemManager, 0, 2, true);
	TestItemConnectable(pItemManager, 0, 3, false);
	TestItemConnectable(pItemManager, 0, 4, false);

	TestItemConnectable(pItemManager, 1, 0, true);
	TestItemConnectable(pItemManager, 1, 1, true);
	TestItemConnectable(pItemManager, 1, 2, true);
	TestItemConnectable(pItemManager, 1, 3, true);
	TestItemConnectable(pItemManager, 1, 4, false);

	TestItemConnectable(pItemManager, 2, 0, true);
	TestItemConnectable(pItemManager, 2, 1, true);
	TestItemConnectable(pItemManager, 2, 2, true);
	TestItemConnectable(pItemManager, 2, 3, true);
	TestItemConnectable(pItemManager, 2, 4, false);

	TestItemConnectable(pItemManager, 3, 0, false);
	TestItemConnectable(pItemManager, 3, 1, true);
	TestItemConnectable(pItemManager, 3, 2, true);
	TestItemConnectable(pItemManager, 3, 3, true);
	TestItemConnectable(pItemManager, 3, 4, true);

	TestItemConnectable(pItemManager, 3, 0, false);
	TestItemConnectable(pItemManager, 3, 1, true);
	TestItemConnectable(pItemManager, 3, 2, true);
	TestItemConnectable(pItemManager, 3, 3, true);
	TestItemConnectable(pItemManager, 3, 4, true);

	delete pItemManager;
}

void TestIsConnectable3x()
{
	vector<string> arrFileName;

	FILE *fptr = fopen("test\\TestIsconnectable3x.txt","r");
	char names[2048];

	while(fscanf(fptr,"%s ",names)==1)
	{
		arrFileName.push_back(names);
	}

	ItemManager* pItemManager = ItemManager::CreateItemManager(arrFileName.size(), arrFileName);
	pItemManager->InitFeatures();

	TestItemConnectable(pItemManager, 0, 0, true);
	TestItemConnectable(pItemManager, 0, 1, false);
	TestItemConnectable(pItemManager, 0, 2, false);
	TestItemConnectable(pItemManager, 0, 3, false);
	TestItemConnectable(pItemManager, 0, 4, false);

	TestItemConnectable(pItemManager, 1, 0, false);
	TestItemConnectable(pItemManager, 1, 1, true);
	TestItemConnectable(pItemManager, 1, 2, true);
	TestItemConnectable(pItemManager, 1, 3, false);
	TestItemConnectable(pItemManager, 1, 4, false);

	TestItemConnectable(pItemManager, 2, 0, false);
	TestItemConnectable(pItemManager, 2, 1, true);
	TestItemConnectable(pItemManager, 2, 2, true);
	TestItemConnectable(pItemManager, 2, 3, true);
	TestItemConnectable(pItemManager, 2, 4, true);

	TestItemConnectable(pItemManager, 3, 0, false);
	TestItemConnectable(pItemManager, 3, 1, false);
	TestItemConnectable(pItemManager, 3, 2, true);
	TestItemConnectable(pItemManager, 3, 3, true);
	TestItemConnectable(pItemManager, 3, 4, true);

	TestItemConnectable(pItemManager, 3, 0, false);
	TestItemConnectable(pItemManager, 3, 1, false);
	TestItemConnectable(pItemManager, 3, 2, true);
	TestItemConnectable(pItemManager, 3, 3, true);
	TestItemConnectable(pItemManager, 3, 4, true);

	delete pItemManager;
}

void TestIsConnectable051x()
{
	vector<string> arrFileName;

	FILE *fptr = fopen("test\\TestIsconnectable051x.txt","r");
	char names[2048];

	while(fscanf(fptr,"%s ",names)==1)
	{
		arrFileName.push_back(names);
	}

	ItemManager* pItemManager = ItemManager::CreateItemManager(arrFileName.size(), arrFileName);
	pItemManager->InitFeatures();

	TestItemConnectable(pItemManager, 0, 0, true);
	TestItemConnectable(pItemManager, 0, 1, true);
	TestItemConnectable(pItemManager, 0, 2, true);

	TestItemConnectable(pItemManager, 1, 0, true);
	TestItemConnectable(pItemManager, 1, 1, true);
	TestItemConnectable(pItemManager, 1, 2, true);

	TestItemConnectable(pItemManager, 2, 0, true);
	TestItemConnectable(pItemManager, 2, 1, true);
	TestItemConnectable(pItemManager, 2, 2, true);

	delete pItemManager;
}

void TestIsConnectable052x()
{
	vector<string> arrFileName;

	FILE *fptr = fopen("test\\TestIsconnectable052x.txt","r");
	char names[2048];

	while(fscanf(fptr,"%s ",names)==1)
	{
		arrFileName.push_back(names);
	}

	ItemManager* pItemManager = ItemManager::CreateItemManager(arrFileName.size(), arrFileName);
	pItemManager->InitFeatures();

	TestItemConnectable(pItemManager, 0, 0, true);
	TestItemConnectable(pItemManager, 0, 1, true);
	TestItemConnectable(pItemManager, 0, 2, true);
	TestItemConnectable(pItemManager, 0, 3, true);

	TestItemConnectable(pItemManager, 1, 0, true);
	TestItemConnectable(pItemManager, 1, 1, true);
	TestItemConnectable(pItemManager, 1, 2, true);
	TestItemConnectable(pItemManager, 1, 3, true);

	TestItemConnectable(pItemManager, 2, 0, true);
	TestItemConnectable(pItemManager, 2, 1, true);
	TestItemConnectable(pItemManager, 2, 2, true);
	TestItemConnectable(pItemManager, 2, 3, true);

	TestItemConnectable(pItemManager, 3, 0, true);
	TestItemConnectable(pItemManager, 3, 1, true);
	TestItemConnectable(pItemManager, 3, 2, true);
	TestItemConnectable(pItemManager, 3, 3, true);

	delete pItemManager;
}

void TestIsConnectable06K42x()
{
	vector<string> arrFileName;

	FILE *fptr = fopen("test\\TestIsconnectable06K42x.txt","r");
	char names[2048];

	while(fscanf(fptr,"%s ",names)==1)
	{
		arrFileName.push_back(names);
	}

	ItemManager* pItemManager = ItemManager::CreateItemManager(arrFileName.size(), arrFileName);
	pItemManager->InitFeatures();

	TestItemConnectable(pItemManager, 0, 0, true);
	TestItemConnectable(pItemManager, 0, 1, true);
	TestItemConnectable(pItemManager, 0, 2, true);
	TestItemConnectable(pItemManager, 0, 3, false);

	TestItemConnectable(pItemManager, 1, 0, true);
	TestItemConnectable(pItemManager, 1, 1, true);
	TestItemConnectable(pItemManager, 1, 2, true);
	TestItemConnectable(pItemManager, 1, 3, false);

	TestItemConnectable(pItemManager, 2, 0, true);
	TestItemConnectable(pItemManager, 2, 1, true);
	TestItemConnectable(pItemManager, 2, 2, true);
	TestItemConnectable(pItemManager, 2, 3, true);

	TestItemConnectable(pItemManager, 3, 0, false);
	TestItemConnectable(pItemManager, 3, 1, false);
	TestItemConnectable(pItemManager, 3, 2, true);
	TestItemConnectable(pItemManager, 3, 3, true);

	delete pItemManager;
}