/****************************************************************************

This program is free software: you can redistribute it and/or modify
it under the terms of the GNU General Public License as published by
the Free Software Foundation, either version 3 of the License, or
(at your option) any later version.

This program is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
GNU General Public License for more details.

You should have received a copy of the GNU General Public License
along with this program.  If not, see <http://www.gnu.org/licenses/>.

-- Copyright 2009 Terence Tsang
-- admin@shinedraw.com
-- http://www.shinedraw.com
-- Your Flash vs Silverlight Repositry

****************************************************************************/


using System;
using System.Collections.Generic;
using System.Linq;
using System.Net;
using System.Windows;
using System.Windows.Controls;
using System.Windows.Documents;
using System.Windows.Input;
using System.Windows.Media;
using System.Windows.Media.Animation;
using System.Windows.Shapes;
using System.Windows.Threading;
using System.Windows.Media.Imaging;
using Kit3D.Windows.Media;
using Kit3D.Windows.Media.Media3D;
using Kit3D.Windows.Controls;
using PhotoSynth;
using System.Windows.Media.Effects;
using System.IO;
using System.Windows.Resources;

/*
*	A 3D Image Space Demonstration in C#
*   from shinedraw.com
*/

namespace PhotoSynth
{
    public partial class ImageSpace3D : UserControl
    {
        private static double _basedistance = 5;
        private static double _distance = 5;
        private Point3D _cameraBasePosition = new Point3D(0, 0, _basedistance);

        public static readonly double FOCUS_OPACITY = 1.0;		// springness
        public static readonly double UNFOCUS_OPACITY = 0.3;		// springness

        public static readonly double WIREFRAME_FOCUS_OPACITY = 0.0;		// springness        
        public static readonly double WIREFRAME_UNFOCUS_OPACITY = 0.3;		// springness

        public static readonly double WIREFRAME_INVISIBLE_OPACITY = 0.0;		// springness
        public static readonly double WIREFRAME_VISIBLE_OPACITY = 0.3;		// springness

        // Hinh 1 va Hinh 2
        public static bool UseMatrix = true;
        private static String Path = "list.txt";

        private static double DISTANCE_MUL = 5;		// springness
        private static double X_MUL = 5;		// springness
        private static double Y_MUL = 5;		// springness
        private static double Z_MUL = 5;		// springness
        private static double ROTATE_UP_MUL = 10;		// springness
        private static double ROTATE_LOOK_MUL = 10;		// springness
        private static double ROTATE_CAM_MUL = 10;		// springness        

		private const int MAX_FRAME_RATE = 24;      // Frame rate
        private const double VIEW_DIMENSION = 20;    // view dimension
		private const double FIELD_OF_VIEW = 75;        // Field of view
		private Viewport3D _viewport;            // 3D Object Container
        private PerspectiveCamera _camera;         // view camera
		
        private List<PhotosynthImage> _images = new List<PhotosynthImage>();        
        private PhotosynthImage _selectedImage = null;
        private Point3D _cameraPosition; // move destination
        private Vector3D _upDirection; // move up direction
        private Vector3D _lookDirection; // move look direction        

        // on enter frame simulator
        private DispatcherTimer _timer;
        private static int FPS = 24;

        private bool _isMoving = false;

        private void Resize()
        {
            //RectangleGeometry rectGeo = new RectangleGeometry();
            //rectGeo.Rect = new Rect(0, 0, Width, Height);
            //LayoutRoot.Clip = rectGeo;
        }

        public ImageSpace3D()
        {
            InitializeComponent();
			App.Current.Host.Settings.MaxFrameRate = MAX_FRAME_RATE;
			
			// Create the camera.
            _camera = new PerspectiveCamera(new Point3D(0, 0, VIEW_DIMENSION), new Vector3D(0, 0, -1), new Vector3D(0, 1, 0), FIELD_OF_VIEW);
            _cameraRotateAngle = _lookRotateAngle = _upRotateAngle = 0;
            // Create Viewport3D as content of window.
            _viewport = new Viewport3D();
            _viewport.Camera = _camera;

            //DropShadowEffect effect = new DropShadowEffect();
            //effect.ShadowDepth = 5;
            //_viewport.Effect = effect;

            //_cameraPosition = new Point3D(0, 0, VIEW_DIMENSION);
            //_camera.Position = new Point3D(0, 0, _distance);
            _cameraPosition = _cameraBasePosition;

            // add all the texts to the stage
            addImages();
            // not enough? create more
            //addImages();

            LayoutRoot.Children.Add(_viewport);
			
            // start the enter frame event
            _timer = new DispatcherTimer();
            _timer.Interval = new TimeSpan(0, 0, 0, 0, 1000 / FPS);
            _timer.Tick +=new EventHandler(_timer_Tick);         
			//Start();
            this.MouseLeftButtonDown += new MouseButtonEventHandler(ImageSpace3D_MouseLeftButtonDown);
            this.ZoomSlider.Value = _distance;
        }


        void ImageSpace3D_MouseLeftButtonDown(object sender, MouseButtonEventArgs e)
        {
            Kit3D.Windows.Media.VisualTreeHelper.HitTest(_viewport, null, HitTest, new PointHitTestParameters(e.GetPosition(_viewport)));
        }

        // only update Destination Camera Position (zooming)
		private void updateDestPosition(PhotosynthImage photosynthImage)
		{
            //return;
            if (photosynthImage == null)
            {
                _cameraPosition = new Point3D(0, 0, _distance);
                return;
            }

            // set the _camera to the position of the text
            if (UseMatrix)
                _cameraPosition = Helper.TransformPoint3D(new Point3D(0, 0, _distance), photosynthImage.MatrixTransform);
            else
                _cameraPosition = Helper.TransformPoint3D(new Point3D(0, 0, _distance), photosynthImage.TransformGroup);
		}

        // update all three : camera position, look vector, up vector
        private void updateDestination(PhotosynthImage photosynthImage)
        {
            //return;
            if (photosynthImage == null)
                return;

            // set the _camera to the position of the text

            if (UseMatrix)
                _cameraPosition = Helper.TransformPoint3D(new Point3D(0, 0, _distance), photosynthImage.MatrixTransform);
            else
                _cameraPosition = Helper.TransformPoint3D(new Point3D(0, 0, _distance), photosynthImage.TransformGroup);
            
            if (UseMatrix)
                _upDirection = Helper.TransformVector3D(new Vector3D(0, 1, 0), photosynthImage.MatrixTransform);
            else
                _upDirection = Helper.RotateVector3D(new Vector3D(0, 1, 0), photosynthImage.Rotations.X, photosynthImage.Rotations.Y, photosynthImage.Rotations.Z);
            _upRotateCenter = new Point3D(0, 0, 0);
            _upRotateAxis = Vector3D.CrossProduct(_camera.UpDirection, _upDirection);
            _upRotateAngle = Helper.GetAngle(_camera.UpDirection, _upDirection);

            _lookDirection = new Vector3D(photosynthImage.RealPosition.X - _cameraPosition.X, photosynthImage.RealPosition.Y - _cameraPosition.Y, photosynthImage.RealPosition.Z - _cameraPosition.Z);
            _lookRotateCenter = new Point3D(0, 0, 0);
            _lookRotateAxis = Vector3D.CrossProduct(_camera.LookDirection, _lookDirection);
            _lookRotateAngle = Helper.GetAngle(_camera.LookDirection, _lookDirection);

            // A : _camera.Position - vi tri hien tai camera
            // B : _cameraPosition - vi tri dich cua camera
            // I : _cameraRotateCenter - trung diem AB
            // _cameraAxis - [OI]x[AB] hoac -[OI]x[AB] sao cho _cameraAxis cung chieu _lookAxis (hop nhau goc nho hon 90)
            //      de dam bao camera luon huong ve phia target plane (chieu xoay camera phu hop chieu xoay look vector)
            _cameraRotateAngle = 180;
            _cameraRotateCenter = new Point3D((_camera.Position.X + _cameraPosition.X) / 2, (_camera.Position.Y + _cameraPosition.Y) / 2, (_camera.Position.Z + _cameraPosition.Z) / 2);
            Vector3D v1 = new Vector3D(_cameraPosition.X - _camera.Position.X, _cameraPosition.Y - _camera.Position.Y, _cameraPosition.Z - _camera.Position.Z);
            Vector3D v2 = new Vector3D(_cameraRotateCenter.X - 0, _cameraRotateCenter.Y - 0, _cameraRotateCenter.Z - 0);
            _cameraRotateAxis = Vector3D.CrossProduct(v1, v2);
            if (_cameraRotateAxis.X == 0 && _cameraRotateAxis.Y == 0 && _cameraRotateAxis.Z == 0)
                _cameraRotateAxis = new Vector3D(0, 1, 0);
            if (Helper.GetAngle(_lookRotateAxis, _cameraRotateAxis) > 90)
                _cameraRotateAxis = -_cameraRotateAxis;
        }

        private HitTestResultBehavior HitTest(HitTestResult result)
        {
            if (_isZooming)
                return HitTestResultBehavior.Stop;
            RayMeshGeometry3DHitTestResult res = result as RayMeshGeometry3DHitTestResult;
            if ((_selectedImage == null) || res.ModelHit != _selectedImage.Model)
            {
                foreach (PhotosynthImage photosynthImage in _images)
                {
                    if (res.ModelHit == photosynthImage.Model)
                    {
                        if (_selectedImage != null)
                            _selectedImage.ModelVisual.Opacity = UNFOCUS_OPACITY;
                        photosynthImage.ModelVisual.Opacity = FOCUS_OPACITY;
                        _selectedImage = photosynthImage;

                        updateDestination(photosynthImage);
                        break;
                    }
                    if (res.ModelHit == photosynthImage.WireframeModel)
                        return HitTestResultBehavior.Continue;
                }
            }
            return HitTestResultBehavior.Stop;
        }

        Vector3D _upRotateAxis; double _upRotateAngle; Point3D _upRotateCenter;
        Vector3D _lookRotateAxis; double _lookRotateAngle; Point3D _lookRotateCenter;
        Vector3D _cameraRotateAxis; double _cameraRotateAngle; Point3D _cameraRotateCenter;        
		
		public void Start()
		{
			_timer.Start();
		}

        private int timeout = 0;
		/////////////////////////////////////////////////////        
		// Handlers
		/////////////////////////////////////////////////////
        void  _timer_Tick(object sender, EventArgs e)
        {
            //timeout++;
            if (timeout == 24 * 5)
            {
                timeout = 0;
                if(_selectedImage != null)
                {
                    int index = _images.IndexOf(_selectedImage);
                    index = (index + 1) % _images.Count;
                    _selectedImage.ModelVisual.Opacity = UNFOCUS_OPACITY;

                    PhotosynthImage photosynthImage = _images[index];
                    photosynthImage.ModelVisual.Opacity = FOCUS_OPACITY;
                    _selectedImage = photosynthImage;
                    updateDestination(photosynthImage);
                }
            }
            //return;
			// move the _camera automatically
			//_destination.z += Z_MOVEMENT;			
            /*
             * Move view coordinate linear
            Point3D cameraPosition = new Point3D(_camera.Position.X + (_cameraPosition.X - _camera.Position.X) / X_MUL,
                                                    _camera.Position.Y + (_cameraPosition.Y - _camera.Position.Y) / Y_MUL,
                                                    _camera.Position.Z + (_cameraPosition.Z - _camera.Position.Z) / Z_MUL);
            Vector3D upDirection = new Vector3D(_camera.UpDirection.X + (_upDirection.X - _camera.UpDirection.X) / X_MUL,
                                                    _camera.UpDirection.Y + (_upDirection.Y - _camera.UpDirection.Y) / Y_MUL,
                                                    _camera.UpDirection.Z + (_upDirection.Z - _camera.UpDirection.Z) / Z_MUL);
            Vector3D lookDirection = new Vector3D(_camera.LookDirection.X + (_lookDirection.X - _camera.LookDirection.X) / X_MUL,
                                                    _camera.LookDirection.Y + (_lookDirection.Y - _camera.LookDirection.Y) / Y_MUL,
                                                    _camera.LookDirection.Z + (_lookDirection.Z - _camera.LookDirection.Z) / Z_MUL);

            _camera.Position = cameraPosition;
            _camera.UpDirection = upDirection;
            _camera.LookDirection = lookDirection;
            */

            if (_isZooming)
            {
                // Zooming animation - not allowed to change target plane
                updateDestPosition(_selectedImage);
                
                if (Math.Abs(_cameraPosition.X - _camera.Position.X) < 0.01
                    && Math.Abs(_cameraPosition.Y - _camera.Position.Y) < 0.01
                    && Math.Abs(_cameraPosition.Z - _camera.Position.Z) < 0.01)
                {
                    // finished
                    _isZooming = false;
                }
                else
                {
                    // zoom : change camera position
                    _curDistance += (_distance - _curDistance) / DISTANCE_MUL;
                    Point3D position = _camera.Position;
                    position.X += (_cameraPosition.X - _camera.Position.X) / X_MUL;
                    position.Y += (_cameraPosition.Y - _camera.Position.Y) / Y_MUL;
                    position.Z += (_cameraPosition.Z - _camera.Position.Z) / Z_MUL;
                    _camera.Position = position;
                }
            }
            else
            {
                // changing target plane, not allowed to zoom-in/out
                double camRotateAngle = _cameraRotateAngle / ROTATE_CAM_MUL;
                if (camRotateAngle > 0.01)
                {
                    _cameraRotateAngle -= camRotateAngle;
                    RotateTransform3D camTransform = new RotateTransform3D(new AxisAngleRotation3D(_cameraRotateAxis, camRotateAngle), _cameraRotateCenter);
                    _camera.Position = camTransform.Value.Transform(_camera.Position);
                }

                double lookRotateAngle = _lookRotateAngle / ROTATE_LOOK_MUL;
                if (lookRotateAngle > 0.01)
                {
                    _lookRotateAngle -= lookRotateAngle;
                    RotateTransform3D lookTransform = new RotateTransform3D(new AxisAngleRotation3D(_lookRotateAxis, lookRotateAngle), _lookRotateCenter);
                    _camera.LookDirection = lookTransform.Value.Transform(_camera.LookDirection);
                }

                double upRotateAngle = _upRotateAngle / ROTATE_UP_MUL;
                if (upRotateAngle > 0.01)
                {
                    _upRotateAngle -= upRotateAngle;
                    RotateTransform3D upTransform = new RotateTransform3D(new AxisAngleRotation3D(_upRotateAxis, upRotateAngle), _upRotateCenter);
                    _camera.UpDirection = upTransform.Value.Transform(_camera.UpDirection);
                }
                if (Math.Abs(camRotateAngle) > 0.01 || Math.Abs(lookRotateAngle) > 0.01 || Math.Abs(upRotateAngle) > 0.01)
                {
                    _isMoving = true;
                    ZoomSlider.IsEnabled = false;
                }
                else
                {
                    // finished
                    _isMoving = false;
                    ZoomSlider.IsEnabled = true;
                }
            }
        }

		/////////////////////////////////////////////////////        
		// Private Methods
		/////////////////////////////////////////////////////	
        Canvas invisibleCanvas; 
        // force silverlight to load image -> get width/height -> create model -> add to viewport
        // -------- silverlight won't load image if it's not in the visible area or being hidden
        private void addImages(){
            invisibleCanvas = new Canvas();
            invisibleCanvas.Opacity = 0;
            LayoutRoot.Children.Add(invisibleCanvas);

            //StreamResourceInfo sri = Application.GetResourceStream(new Uri(string.Format("/PhotySynth;component/{0}", Path), UriKind.Relative));
            StreamResourceInfo sri = Application.GetResourceStream(new Uri(Path, UriKind.Relative));
            if (UseMatrix == true)
            {
                #region UseMatrix
                //using (TextReader reader = File.OpenText(Path))
                using(StreamReader reader = new StreamReader(sri.Stream))
                {
                    string line;
                    while ((line = reader.ReadLine()) != null)
                    {
                        string url = line;
                        double[,] values = new double[4, 4];
                        string[] bits;

                        for (int i = 0; i < 4; i++)
                        {
                            line = reader.ReadLine();
                            bits = line.Split(' ');
                            for (int j = 0; j < 4; j++)
                            {
                                double value = 0;
                                if (double.TryParse(bits[j], out value))
                                {
                                    values[i, j] = value;
                                }
                            }
                        }
                        Matrix3D transformationMat = 
                            new Matrix3D(   values[0, 0], values[0, 1], values[0, 2], values[0, 3],
                                            values[1, 0], values[1, 1], values[1, 2], values[1, 3],
                                            values[2, 0], values[2, 1], values[2, 2], values[2, 3],
                                            values[3, 0], values[3, 1], values[3, 2], values[3, 3]);
                        //transformationMat.Invert();

                        PhotosynthImage photosynthImage = new PhotosynthImage(url, transformationMat);
                        photosynthImage.BitmapImageLoaded += new EventHandler<EventArgs>(photosynthImage_BitmapImageLoaded);
                        _images.Add(photosynthImage);

                        Image img = new Image();
                        img.Source = photosynthImage.BitmapImage;
                        invisibleCanvas.Children.Add(img);
                    }
                }
                #endregion
            }
            else
            {
                #region UseAngle
                using (StreamReader reader = new StreamReader(sri.Stream))
                {
                    string line;
                    while ((line = reader.ReadLine()) != null)
                    {
                        string url = line;
                        double[] values = new double[3];
                        string[] bits;

                        line = reader.ReadLine();
                        bits = line.Split(' ');
                        for (int j = 0; j < 3; j++)
                        {
                            double value = 0;
                            if (double.TryParse(bits[j], out value))
                                values[j] = value;
                            else
                                values[j] = 0;
                        }
                        Point3D rotation = new Point3D(values[0], values[1], values[2]);


                        line = reader.ReadLine();
                        bits = line.Split(' ');
                        for (int j = 0; j < 3; j++)
                        {
                            double value = 0;
                            if (double.TryParse(bits[j], out value))
                                values[j] = value;
                            else
                                values[j] = 0;
                        }
                        Point3D translation = new Point3D(values[0], values[1], values[2]);

                        PhotosynthImage photosynthImage = new PhotosynthImage(url, rotation, translation);
                        photosynthImage.BitmapImageLoaded += new EventHandler<EventArgs>(photosynthImage_BitmapImageLoaded);
                        _images.Add(photosynthImage);

                        Image img = new Image();
                        img.Source = photosynthImage.BitmapImage;
                        invisibleCanvas.Children.Add(img);
                    }
                }
                #endregion
            }
        }

        void photosynthImage_BitmapImageLoaded(object sender, EventArgs e)
        {
            PhotosynthImage photosynthImage = sender as PhotosynthImage;
            if (photosynthImage != null)
            {
                _viewport.Children.Add(photosynthImage.createNewModel());
                _viewport.Children.Add(photosynthImage.createNewModel2());
            }
        }

		
        private void UserControl_SizeChanged(object sender, System.Windows.SizeChangedEventArgs e)
        {
        	// TODO: Add event handler implementation here.
			Resize();
        }

        private void Slider_ValueChanged(object sender, System.Windows.RoutedPropertyChangedEventArgs<double> e)
        {
        	// TODO: Add event handler implementation here.
            Zooming(e.NewValue);
        }
        
        private bool _isZooming = false;
        private double _oldDistance;
        private double _curDistance;

        private void Zooming(double value)
        {
            if (!_isMoving)
            {
                _oldDistance = _curDistance = _distance;
                _distance = value;
                _isZooming = true;
            }
        }

        private int rotateX = 0;
        private void RotateX_ValueChanged(object sender, RoutedPropertyChangedEventArgs<double> e)
        {
            
        }

        private void checkBox1_Unchecked(object sender, RoutedEventArgs e)
        {
            foreach(PhotosynthImage img in _images)
            {
                img.WireframeModelVisual.Opacity = WIREFRAME_INVISIBLE_OPACITY;
            }
        }

        private void checkBox1_Checked(object sender, RoutedEventArgs e)
        {
            foreach (PhotosynthImage img in _images)
            {
                img.WireframeModelVisual.Opacity = WIREFRAME_VISIBLE_OPACITY;
            }
        }
    }
}
