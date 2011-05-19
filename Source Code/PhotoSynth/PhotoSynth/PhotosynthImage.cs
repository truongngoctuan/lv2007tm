using System;
using System.Collections.Generic;
using System.Text;
using System.Windows;
using System.Windows.Controls;
using System.Windows.Data;
using System.Windows.Documents;
using System.Windows.Input;
using System.Windows.Media;
using System.Windows.Media.Imaging;
using System.Windows.Shapes;
using Kit3D.Windows.Media.Media3D;
using Kit3D.Windows.Media;

namespace PhotoSynth
{
	public class PhotosynthImage : Canvas
	{
        static float base_focal = 10;
        // Random image's pose
        private static double MIN_X = -5; private static double MAX_X = 5;
        private static double MIN_Y = -5; private static double MAX_Y = 5;
        private static double MIN_Z = -5; private static double MAX_Z = 5;

        private static double MIN_ROTATE_X = -45; private static double MAX_ROTATE_X = 45;
        private static double MIN_ROTATE_Y = -45; private static double MAX_ROTATE_Y = 45;
        private static double MIN_ROTATE_Z = -45; private static double MAX_ROTATE_Z = 45;

        private static int seed = (int)DateTime.Now.Ticks;
        
        public static Point3D BasePosition = new Point3D(0, 0, -base_focal);
        public Point3D RealPosition;

        public Point3D BaseTranslation = new Point3D(BasePosition.X, BasePosition.Y, BasePosition.Z);
		public Point3D Translations;
		public Point3D Rotations;
        public Transform3DGroup TransformGroup;

        public Matrix3D BaseMatrix = new Matrix3D(1, 0, 0, 0,
                                                    0, 1, 0, 0,
                                                    0, 0, 1, 0,
                                                    BasePosition.X, BasePosition.Y, BasePosition.Z, 1);
        public Matrix3D TransformationMat = Matrix3D.Identity;
        public MatrixTransform3D MatrixTransform;

        public Vector3D Axis;
        public float Angle;

        public BitmapImage BitmapImage;
        public ImageBrush ImageBrush;
        public GeometryModel3D Model;
        public ModelVisual3D ModelVisual;

        public GeometryModel3D WireframeModel;
        public ModelVisual3D WireframeModelVisual;
        public double m_Width = 0;  // kich thuoc that cua anh
        public double m_Height = 0; // kich thuoc that cua anh

        private const int BASE_METRIC = 128;

        public event EventHandler<EventArgs> BitmapImageLoaded;

        static int count = 0;        
        public PhotosynthImage(string url, Matrix3D transformationMat)
        {
            TransformationMat = transformationMat;
            MatrixTransform = new MatrixTransform3D(Matrix3D.Multiply(BaseMatrix, TransformationMat));
            RealPosition = Helper.TransformPoint3D(new Point3D(0, 0, 0), MatrixTransform);

            BitmapImage = new BitmapImage(new Uri(url, UriKind.Relative));
            ImageBrush = new ImageBrush();
            ImageBrush.ImageSource = BitmapImage;
            BitmapImage.ImageOpened += new EventHandler<RoutedEventArgs>(BitmapImage_ImageOpened);
        }
        public PhotosynthImage(string url, Point3D rotation, Point3D translation)
        {
            Rotations = rotation;
            Translations = translation;

            TransformGroup = new Transform3DGroup();
            TransformGroup.Children.Add(new TranslateTransform3D(BasePosition.X, BasePosition.Y, BasePosition.Z));
            if (Rotations.X != 0)
                TransformGroup.Children.Add(new RotateTransform3D(new AxisAngleRotation3D(new Vector3D(1, 0, 0), Rotations.X), new Point3D(0, 0, 0)));
            if (Rotations.Y != 0)
                TransformGroup.Children.Add(new RotateTransform3D(new AxisAngleRotation3D(new Vector3D(0, 1, 0), Rotations.Y), new Point3D(0, 0, 0)));
            if (Rotations.Z != 0)
                TransformGroup.Children.Add(new RotateTransform3D(new AxisAngleRotation3D(new Vector3D(0, 0, 1), Rotations.Z), new Point3D(0, 0, 0)));
            TransformGroup.Children.Add(new TranslateTransform3D(Translations.X, Translations.Y, Translations.Z));

            RealPosition = Helper.TransformPoint3D(new Point3D(0, 0, 0), TransformGroup);

            BitmapImage = new BitmapImage(new Uri(url, UriKind.Relative));
            ImageBrush = new ImageBrush();
            ImageBrush.ImageSource = BitmapImage;
            BitmapImage.ImageOpened += new EventHandler<RoutedEventArgs>(BitmapImage_ImageOpened);
        }

        void BitmapImage_ImageOpened(object sender, RoutedEventArgs e)
        {            
            BitmapImage bi = (BitmapImage)sender;
            m_Width = bi.PixelWidth;
            m_Height = bi.PixelHeight;

            BitmapImageLoaded.Invoke(this, EventArgs.Empty);
        }

        // create a new texture mapped plane
        public ModelVisual3D createNewModel()
        {
            GeometryModel3D model = new GeometryModel3D();
            model.Geometry = generatePlaneMesh();
            model.Material = new DiffuseMaterial(new Kit3DBrush(ImageBrush, (int)m_Width, (int)m_Height));
            model.SeamSmoothing = 1;
            model.BackMaterial = new DiffuseMaterial(new Kit3DBrush(new SolidColorBrush(Colors.Black)));
            //model.BackMaterial = model.Material;

            Transform3D transform3D = null;
            if (ImageSpace3D.UseMatrix)
            {
                transform3D = MatrixTransform;                
            }
            else
            {
                // Create the transform
                transform3D = TransformGroup;
            }            

            // create the model based on the material and transform
            ModelVisual3D modvis = new ModelVisual3D();
            modvis.Transform = transform3D;
            modvis.Content = model;
            modvis.Opacity = ImageSpace3D.UNFOCUS_OPACITY;
            //modvis.Opacity = 1.0;

            Model = model;
            ModelVisual = modvis;
            return modvis;
        }

        public ModelVisual3D createNewModel2()
        {
            GeometryModel3D model = new GeometryModel3D();
            model.Geometry = generateViewMesh();
            model.Material = new DiffuseMaterial(new Kit3DBrush(new SolidColorBrush(Colors.White)));
            model.SeamSmoothing = 1;
            //model.BackMaterial = new DiffuseMaterial(new Kit3DBrush(new SolidColorBrush(Colors.Black)));
            model.BackMaterial = model.Material;

            Transform3D transform3D = null;
            if (ImageSpace3D.UseMatrix)
            {
                transform3D = MatrixTransform;
            }
            else
            {
                // Create the transform
                transform3D = TransformGroup;
            }

            // create the model based on the material and transform
            ModelVisual3D modvis = new ModelVisual3D();
            modvis.Transform = transform3D;
            modvis.Content = model;
            modvis.Opacity = ImageSpace3D.WIREFRAME_INVISIBLE_OPACITY;

            WireframeModel = model;
            WireframeModelVisual = modvis;
            return modvis;
        }


        // a standard texture mapping mesh
        private MeshGeometry3D generatePlaneMesh()
        {
            double width_metric = m_Width / BASE_METRIC;
            double height_metric = m_Height / BASE_METRIC;

            MeshGeometry3D mesh = new MeshGeometry3D();
            mesh.Positions = new Point3DCollection
            {
                new Point3D(-width_metric/2, height_metric/2, 0),
                new Point3D(width_metric/2, height_metric/2, 0),
                new Point3D(-width_metric/2, -height_metric/2, 0),
                new Point3D(width_metric/2, -height_metric/2, 0)
            };

            //mesh.Positions = new Point3DCollection
            //{
            //    new Point3D(-1, 1, 0),
            //    new Point3D(1, 1, 0),
            //    new Point3D(-1, -1, 0),
            //    new Point3D(1, -1, 0)
            //};

            mesh.TriangleIndices = new Int32Collection
            {
                0, 2, 1,
                1, 2, 3
            };

            mesh.TextureCoordinates = new Kit3D.Windows.Media.PointCollection
            {
                new Point(0, 0),
                new Point(1, 0),
                new Point(0, 1),
                new Point(1, 1)
            };

            return mesh;
        }

        private MeshGeometry3D generateViewMesh()
        {
            double width_metric = m_Width / BASE_METRIC;
            double height_metric = m_Height / BASE_METRIC;
            MeshGeometry3D mesh = new MeshGeometry3D();
            mesh.Positions = new Point3DCollection
            {
                new Point3D(0, 0, base_focal),
                new Point3D(-width_metric/2, height_metric/2, 0),
                new Point3D(width_metric/2, height_metric/2, 0),
                new Point3D(width_metric/2, -height_metric/2, 0),
                new Point3D(-width_metric/2, -height_metric/2, 0)                
            };

            //mesh.Positions = new Point3DCollection
            //{
            //    new Point3D(-1, 1, 0),
            //    new Point3D(1, 1, 0),
            //    new Point3D(-1, -1, 0),
            //    new Point3D(1, -1, 0)
            //};

            mesh.TriangleIndices = new Int32Collection
            {
                1, 0, 2,
                2, 0, 3,
                3, 0, 4,
                4, 0, 1
            };

            //mesh.TextureCoordinates = new Kit3D.Windows.Media.PointCollection
            //{
            //    new Point(0, 0),
            //    new Point(1, 0),
            //    new Point(0, 1),
            //    new Point(1, 1)
            //};

            return mesh;
        }
	}
}