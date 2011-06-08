

using System.IO;
using System.Collections.Generic;
using Microsoft.Xna.Framework;
using _3DPresentation.Models;
using System;
namespace _3DPresentation.Controllers
{
    public class MatchedFeatureController
    {
        List<MatchedFeaturePair> listPairs;
        int nTried = 0;

        static int MIN_DISTANCE = 300;
        static int MAX_TOLERANCE = 5;

        MyModel model1;
        MyModel model2;
        public MatchedFeatureController(MyModel m1, MyModel m2)
        {
            model1 = m1;
            model2 = m2;
        }

        public void GetPairs(FileInfo fileInfo)
        {
            List<MatchedFeaturePair> pairs = new List<MatchedFeaturePair>();
            using (StreamReader stream = fileInfo.OpenText())
            {
                string strN = stream.ReadLine();
                nTried = int.Parse(strN);

                strN = stream.ReadLine();
                MIN_DISTANCE = int.Parse(strN);
                strN = stream.ReadLine();
                MAX_TOLERANCE = int.Parse(strN);

                strN = stream.ReadLine();
                int n = int.Parse(strN);
                for (int line = 0; line < n; line++)
                {
                    string ss = stream.ReadLine();
                    string[] Items = ss.Split(new char[] { ' ' });

                    int x1, y1, x2, y2;
                    x1 = int.Parse(Items[0]);
                    y1 = int.Parse(Items[1]);
                    x2 = int.Parse(Items[2]);
                    y2 = int.Parse(Items[3]);

                    Vector3 p1 = model1.PixelToPoint(x1, y1);
                    Vector3 p2 = model2.PixelToPoint(x2, y2);

                    if (p1 == Vector3.Zero || p2 == Vector3.Zero)
                        continue;
                    MatchedFeaturePair p = new MatchedFeaturePair();
                    p.destPosition = p1;
                    p.movingPoint = p2;

                    pairs.Add(p);
                }
            }
            listPairs = pairs;
        }
        public  MatchedFeaturePair[] GetBestPairs()
        {
            int nTriedCount = 0;
            MatchedFeaturePair[] bestPairs = new MatchedFeaturePair[3];
            for (int i = 0; i < listPairs.Count; i++)
            {
                for (int j = 0; j < listPairs.Count; j++)
                {
                    if (i == j)
                        continue;
                    double distance12a = Vector3.Distance(listPairs[i].destPosition, listPairs[j].destPosition);
                    double distance12b = Vector3.Distance(listPairs[i].movingPoint, listPairs[j].movingPoint);
                    if (distance12a < MIN_DISTANCE || distance12b < MIN_DISTANCE)
                        continue;
                    if (Math.Abs(distance12a - distance12b) < MAX_TOLERANCE)
                    {
                        for (int k = 0; k < listPairs.Count; k++)
                        {
                            if (k == i || k == j)
                                continue;
                            double distance13a = Vector3.Distance(listPairs[i].destPosition, listPairs[k].destPosition);
                            double distance13b = Vector3.Distance(listPairs[i].movingPoint, listPairs[k].movingPoint);

                            double distance23a = Vector3.Distance(listPairs[j].destPosition, listPairs[k].destPosition);
                            double distance23b = Vector3.Distance(listPairs[j].movingPoint, listPairs[k].movingPoint);

                            if (distance13a < MIN_DISTANCE || distance13b < MIN_DISTANCE)
                                continue;
                            if (distance23a < MIN_DISTANCE || distance23b < MIN_DISTANCE)
                                continue;
                            if (Math.Abs(distance13a - distance13b) < MAX_TOLERANCE && Math.Abs(distance23a - distance23b) < MAX_TOLERANCE)
                            {
                                nTriedCount++;
                                if (nTriedCount > nTried)
                                {
                                    bestPairs[0] = listPairs[i];
                                    bestPairs[1] = listPairs[j];
                                    bestPairs[2] = listPairs[k];
                                    return bestPairs;
                                }
                            }
                        }
                    }
                }
            }
            return null;
        }
    }
}
