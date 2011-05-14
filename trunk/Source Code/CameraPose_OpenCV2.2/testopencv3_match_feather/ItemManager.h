#pragma once
#include "Item.h";
#include <string>
#include <vector>
using namespace std;

class ItemManager
{
	int nItems;
	Item* pItems;
	bool* pIsConnected;
	bool** pIsTried;

	int root;
	CvMat *K;
	CvMat *D;
private:
	ItemManager();
	bool IsConnected(int index);
	bool IsConnectable(int item1, int item2);
	bool IsTried(int item1, int item2);
	int GetNextTarget();
public:	
	static ItemManager* CreateItemManager(int n, vector<string> filenames, int root = 0);
	~ItemManager(void);
	void Print(ostream &out);

	void InitFeatures();
	void BuildTree();	
};

