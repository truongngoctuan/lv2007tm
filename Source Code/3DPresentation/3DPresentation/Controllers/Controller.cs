using Microsoft.Xna.Framework;
using System.Collections.Generic;
using _3DPresentation.Models;
using System.Windows.Threading;
using System;
using System.IO;

namespace _3DPresentation.Controllers
{
    public struct MatchedFeaturePair
    {
        public Vector3 destPosition;
        public Vector3 movingPoint;
        public MatchedFeaturePair(Vector3 dest, Vector3 moving)
        {
            destPosition = dest;
            movingPoint = moving;
        }
        public bool IsEqual(MatchedFeaturePair rhs)
        {
            if (destPosition == rhs.destPosition || movingPoint == rhs.movingPoint)
                return true;
            return false;
        }
    }
    public class Controller
    {
        private static List<Controller> sControllers = new List<Controller>();
        MyModel DestModel;
        MyModel MovingModel;
        List<MatchedFeaturePair> matchedFeaturePair;
        MatchedFeatureController matchController;
        FileInfo filePairs = null;

        DispatcherTimer timer;
        public Controller(MyModel destModel, MyModel movingModel, FileInfo pairs)
        {
            DestModel = destModel;
            MovingModel = movingModel;
            matchedFeaturePair = new List<MatchedFeaturePair>();
            matchController = new MatchedFeatureController(destModel, movingModel);
            InitAnimate(pairs);
        }

        public void Reset()
        {
            InitAnimate(filePairs);
        }

        private void InitAnimate(FileInfo pairs)
        {
            filePairs = pairs;
            matchController.GetPairs(pairs);
            MatchedFeaturePair[] bestPair = matchController.GetBestPairs();
            if (bestPair != null)
            {
                // Found requested solution 
                this.AddMatchedFeaturePair(bestPair[0]);
                this.AddMatchedFeaturePair(bestPair[1]);
                this.AddMatchedFeaturePair(bestPair[2]);

                DestModel.marker1 = bestPair[0].destPosition;
                DestModel.marker2 = bestPair[1].destPosition;
                DestModel.marker3 = bestPair[2].destPosition;

                MovingModel.marker1 = bestPair[0].movingPoint;
                MovingModel.marker2 = bestPair[1].movingPoint;
                MovingModel.marker3 = bestPair[2].movingPoint;
            }
            else
            {
                // Not found
                DestModel.marker1 = Vector3.Zero;
                DestModel.marker2 = Vector3.Zero;
                DestModel.marker3 = Vector3.Zero;

                MovingModel.marker1 = Vector3.Zero;
                MovingModel.marker2 = Vector3.Zero;
                MovingModel.marker3 = Vector3.Zero;
            }
        }

        private bool AddMatchedFeaturePair(MatchedFeaturePair pair)
        {
            foreach (MatchedFeaturePair p in matchedFeaturePair)
            {
                if (p.destPosition == pair.destPosition || p.destPosition == pair.movingPoint)
                    return false;
                if (p.movingPoint == pair.destPosition || p.movingPoint == pair.movingPoint)
                    return false;                
            }
            matchedFeaturePair.Add(pair);
            return true;
        }

        public bool ClearControllerList()
        {
            bool result = false;
            if (sControllers.Count > 0)
                result = true;
            sControllers.Clear();
            return result;
        }

        private bool AddController()
        {
            foreach (Controller controller in sControllers)
            {
                if (controller == this)
                    continue;
                if (controller.DestModel == this.DestModel && controller.MovingModel == this.MovingModel)
                    return false;
            }
            //if (sControllers.Contains(this))
            //    return false;
            sControllers.Add(this);
            return true;
        }

        public void Run()
        {
            if (matchedFeaturePair.Count < 3)
                return;
            if (AddController() == false)
                return;

            if (timer != null)
            {
                timer.Stop();
                timer = null;
            }

            timer = new DispatcherTimer();
            timer.Tick += new System.EventHandler(timer_Tick);
            timer.Interval = System.TimeSpan.FromMilliseconds(100);

            // MovingPoints in World Coordinate System
            destPoints = new Vector3[3];
            destPoints[0] = matchedFeaturePair[0].destPosition;
            destPoints[1] = matchedFeaturePair[1].destPosition;
            destPoints[2] = matchedFeaturePair[2].destPosition;
            destPoints = Util.TransformPoints(DestModel.WorldMatrix, destPoints);

            // MovingPoints in World Coordinate System
            movingPoints = new Vector3[3];
            movingPoints[0] = matchedFeaturePair[0].movingPoint;
            movingPoints[1] = matchedFeaturePair[1].movingPoint;
            movingPoints[2] = matchedFeaturePair[2].movingPoint;
            movingPoints = Util.TransformPoints(MovingModel.WorldMatrix, movingPoints);

            // Precalculation
            originalTransformation = MovingModel.WorldMatrix;
            finalTransformation = CalculateFinalTransformation();
            finalMovingModelMatrix = originalTransformation * finalTransformation;

            // MovingPoints in World Coordinate System
            movingPoints = new Vector3[3];
            movingPoints[0] = matchedFeaturePair[0].movingPoint;
            movingPoints[1] = matchedFeaturePair[1].movingPoint;
            movingPoints[2] = matchedFeaturePair[2].movingPoint;
            movingPoints = Util.TransformPoints(MovingModel.WorldMatrix, movingPoints);
            //movingPoints = TransformPoints(finalMovingModelMatrix, movingPoints);

            // Start animation
            currentTranslation = Vector3.Zero;
            currentRotation1 = 0;
            currentRotation2 = 0;
            currentStage = Stage.Stage1;
            timer.Start();
        }

        private Matrix originalTransformation;
        private Matrix finalTransformation;
        private Matrix finalMovingModelMatrix;
        private Vector3 finalTranslation; private Vector3 currentTranslation;
        private float finalRotation1; private Vector3 rotationAxis1; private float currentRotation1;
        private float finalRotation2; private Vector3 rotationAxis2; private float currentRotation2;

        Vector3[] destPoints;
        Vector3[] movingPoints;
        private Matrix CalculateFinalTransformation()
        {
            Matrix finalMat = Matrix.Identity;
            if (destPoints[0] != movingPoints[0])
            {
                // First : Translation  => One feature fixed
                Vector3 translationVector = destPoints[0] - movingPoints[0];
                Matrix matrix = Matrix.CreateTranslation(translationVector);                 

                // tranfrom movingPoints
                movingPoints = Util.TransformPoints(matrix, movingPoints);

                finalTranslation = translationVector;
                finalMat *= matrix;
            }
            if (destPoints[1] != movingPoints[1])
            {
                // Second : Rotation  => Two features fixed
                Vector3 v1 = destPoints[1] - destPoints[0];
                Vector3 v2 = movingPoints[1] - movingPoints[0];

                // See wikipedia : http://en.wikipedia.org/wiki/Cross_product
                // axis : rotation axis from v2 to v1
                // angle : must less than 180 to match with the rotation axis
                Vector3 axis = Vector3.Cross(v2, v1);
                float angle = (float)Util.GetAngle(v2, v1);

                // MUST NORMALIZE THE AXIS VECTOR
                axis.Normalize();

                Matrix preTranslate = Matrix.CreateTranslation(-movingPoints[0]);
                Matrix matrix = Matrix.CreateFromAxisAngle(axis, ConvertToRadian(angle));
                Matrix postTranslate = Matrix.CreateTranslation(movingPoints[0]);
                matrix = preTranslate * matrix * postTranslate;

                // tranfrom movingPoints
                movingPoints = Util.TransformPoints(matrix, movingPoints);

                rotationAxis1 = axis;
                finalRotation1 = angle;
                finalMat *= matrix;
            }
            if (destPoints[2] != movingPoints[2])
            {
                // Third : Rotation  => Three features fixed
                Vector3 destv1 = destPoints[2] - destPoints[0];
                Vector3 destv2 = destPoints[1] - destPoints[0];
                Vector3 destnormal = Vector3.Cross(destv2, destv1); // or destv1, destv2
                destnormal.Normalize();

                Vector3 movev1 = movingPoints[2] - movingPoints[0];
                Vector3 movev2 = movingPoints[1] - movingPoints[0];
                Vector3 movenormal = Vector3.Cross(movev2, movev1); // or destv1, destv2
                movenormal.Normalize();

                // See wikipedia : http://en.wikipedia.org/wiki/Cross_product
                // axis : rotation axis from v2 to v1, match with an less-than-180-degree angle
                // angle : will be less than 180 to match with the rotation axis
                Vector3 axis = Vector3.Cross(movenormal, destnormal);
                float angle = (float)Util.GetAngle(movenormal, destnormal);

                // MUST NORMALIZE THE AXIS VECTOR
                axis.Normalize();

                Matrix preTranslate = Matrix.CreateTranslation(-movingPoints[0]);
                Matrix matrix = Matrix.CreateFromAxisAngle(axis, ConvertToRadian(angle));
                Matrix postTranslate = Matrix.CreateTranslation(movingPoints[0]);
                matrix = preTranslate * matrix * postTranslate;

                // tranfrom movingPoints
                movingPoints = Util.TransformPoints(matrix, movingPoints);

                rotationAxis2 = axis;
                finalRotation2 = angle;
                finalMat *= matrix;
            }
            // MUST BE MATCH BY NOW
            // ASSERT MATCHING
            return finalMat;
        }

        private float ConvertToRadian(float angle)
        {
            return MathHelper.ToRadians(angle);            
        }

        private static float SPRING = 10;

        private static float LAST_ANIMATE_DISTANCE = 5.0f;
        private static float LAST_ANIMATE_ANGLE = 0.5f;
        
        private static float MIN_DISTANCE = 0.1f;
        private static float MIN_ANGLE = 0.1f;

        //non-public
        enum Stage { Stage1, Stage2, Stage3, Finished, Aborted }
        Stage currentStage;

        public bool isEnable = false;
        void timer_Tick(object sender, System.EventArgs e)
        {
            if (!isEnable)
                return;
            float distance = 0;
            if (currentStage == Stage.Stage1)
            {
                if ((distance = Vector3.Distance(destPoints[0], movingPoints[0])) > MIN_DISTANCE)
                {
                    // First : Translation  => One feature fixed
                    Vector3 translateVector = finalTranslation - currentTranslation;
                    if (distance > LAST_ANIMATE_DISTANCE)
                        translateVector /= SPRING;

                    currentTranslation += translateVector;
                    Matrix matrix = Matrix.CreateTranslation(translateVector);
                    MovingModel.WorldMatrix *= matrix;

                    // transform movingPoints
                    movingPoints = Util.TransformPoints(matrix, movingPoints);
                }
                else
                {
                    currentStage = Stage.Stage2;
                    isEnable = false;
                }
            }
            else if (currentStage == Stage.Stage2)
            {
                //if ((distance = Vector3.Distance(destPoints[1].destPosition, movingPoints[1])) > MIN_DISTANCE)
                float angle = 0;
                if((angle = finalRotation1 - currentRotation1) > MIN_ANGLE)
                {
                    // Second : Rotation  => Two features fixed                    
                    if (angle > LAST_ANIMATE_ANGLE)
                        angle /= SPRING;
                    currentRotation1 += angle;

                    Matrix preTranslate = Matrix.CreateTranslation(-movingPoints[0]);
                    Matrix matrix = Matrix.CreateFromAxisAngle(rotationAxis1, ConvertToRadian(angle));
                    Matrix postTranslate = Matrix.CreateTranslation(movingPoints[0]);
                    matrix = preTranslate * matrix * postTranslate;
                    MovingModel.WorldMatrix *= matrix;

                    // transform movingPoints
                    movingPoints = Util.TransformPoints(matrix, movingPoints);
                }
                else
                {
                    currentStage = Stage.Stage3;
                    isEnable = false;
                }
            }
            else if (currentStage == Stage.Stage3)
            {
                //if ((distance = Vector3.Distance(destPoints[2].destPosition, movingPoints[2])) > MIN_DISTANCE)
                float angle = 0;
                if ((angle = finalRotation2 - currentRotation2) > MIN_ANGLE)
                {
                    // Third : Rotation  => Three features fixed
                    if (angle > LAST_ANIMATE_ANGLE)
                        angle /= SPRING;
                    currentRotation2 += angle;

                    Matrix preTranslate = Matrix.CreateTranslation(-movingPoints[0]);
                    Matrix matrix = Matrix.CreateFromAxisAngle(rotationAxis2, ConvertToRadian(angle));
                    Matrix postTranslate = Matrix.CreateTranslation(movingPoints[0]);
                    matrix = preTranslate * matrix * postTranslate;
                    MovingModel.WorldMatrix *= matrix;

                    // transform movingPoints
                    movingPoints = Util.TransformPoints(matrix, movingPoints);
                }
                else
                {
                    currentStage = Stage.Finished;
                    isEnable = false;
                }
            }
            else if(currentStage == Stage.Finished)
            {
                // DONE ANIMATING, ASSIGN FINAL MAT FROM PRECALCULATION TO MODEL 
                MovingModel.WorldMatrix = finalMovingModelMatrix;

                timer.Stop();
                timer = null;
            }
            else if (currentStage == Stage.Aborted)
            {
                timer.Stop();
                timer = null;
            }
        }

        // Export to ply format
        public bool ExportMergedMesh(FileInfo outFile)
        {
            bool bResult = true;
            try
            {
                Partition.ExportType = Partition.VertexExportType.PositionColor;

                StreamWriter sw = new StreamWriter(outFile.OpenWrite());
                //StreamWriter sw = new StreamWriter(File.OpenWrite(outFile.FullName));
                long NumberOfAcceptableVertices = DestModel.NumberOfAcceptableVertices + MovingModel.NumberOfAcceptableVertices;
                //sw.WriteLine(NumberOfAcceptableVertices);

                if (Partition.ExportType == Partition.VertexExportType.Position)
                {
                    sw.WriteLine("ply");
                    sw.WriteLine("format ascii 1.0");
                    sw.WriteLine("element vertex " + NumberOfAcceptableVertices);
                    sw.WriteLine("property float32 x");
                    sw.WriteLine("property float32 y");
                    sw.WriteLine("property float32 z");
                    sw.WriteLine("end_header");
                }
                else if (Partition.ExportType == Partition.VertexExportType.PositionColor)
                {
                    sw.WriteLine("ply");
                    sw.WriteLine("format ascii 1.0");
                    sw.WriteLine("element vertex " + NumberOfAcceptableVertices);
                    sw.WriteLine("property float32 x");
                    sw.WriteLine("property float32 y");
                    sw.WriteLine("property float32 z");
                    sw.WriteLine("property uchar red");
                    sw.WriteLine("property uchar green");
                    sw.WriteLine("property uchar blue");
                    sw.WriteLine("end_header");
                }
                else if (Partition.ExportType == Partition.VertexExportType.PositionColorNormal)
                {
                    sw.WriteLine("ply");
                    sw.WriteLine("format ascii 1.0");
                    sw.WriteLine("element vertex " + NumberOfAcceptableVertices);
                    sw.WriteLine("property float32 x");
                    sw.WriteLine("property float32 y");
                    sw.WriteLine("property float32 z");
                    sw.WriteLine("property uchar red");
                    sw.WriteLine("property uchar green");
                    sw.WriteLine("property uchar blue");
                    sw.WriteLine("property float32 nx");
                    sw.WriteLine("property float32 ny");
                    sw.WriteLine("property float32 nz");
                    sw.WriteLine("end_header");
                }
                DestModel.ExportMesh(sw);
                MovingModel.ExportMesh(sw);
                sw.Close();
            }
            catch (Exception ex)
            {
                bResult = false;
            }
            return bResult;
        }
    }
}
