using System.Collections.Generic;
using System.ComponentModel;
using System.Windows;
using System.Windows.Controls;
using System.Windows.Input;
using Microsoft.Xna.Framework;

namespace Babylon
{
    public partial class BabylonSurface
    {
        readonly Engine engine;
        Scene scene;
        bool mouseCaptured;
        bool isFullscreen;
        readonly List<MoveDirection> moves = new List<MoveDirection>();

        //nhminh
        public void SetCustomScene(Scene customScene)
        {
            scene = null;
            scene = customScene;
        }

        public BabylonSurface()
        {
            InitializeComponent();

            if (Application.Current.RootVisual != null && DesignerProperties.GetIsInDesignMode(Application.Current.RootVisual))
                return;
            engine = new Engine();

            Application.Current.Host.Content.FullScreenChanged += (s, e) =>
                                                                      {
                                                                          IsFullscreen = false;
                                                                      };

            scene = new Scene("BabylonScene", Engine);
        }

        public Engine Engine
        {
            get { return engine; }
        }

        public Scene Scene
        {
            get { return scene; }
        }

        void OnDraw(object sender, DrawEventArgs e)
        {
            //nhminh
            //if (engine.Device == null)
            //{
                engine.Device = e.GraphicsDevice;
            //}

            engine.BeginFrame(e);

            if (scene != null && scene.ActiveCamera != null)
            {
                scene.Render();

                lock (moves)
                {
                    foreach (MoveDirection move in moves)
                    {
                        scene.ControlManager.CheckKeyboard(move, e.DeltaTime.TotalMilliseconds);
                    }
                }
            }

            engine.EndFrame();
        }

        void HandleMouseUp()
        {
            if (Scene == null || Scene.ActiveCamera == null || IsFullscreen)
                return;

            if (mouseCaptured)
            {
                mouseCaptured = false;

                Scene.ControlManager.HandleMouseUp();
            }
        }

        private void UserControl_MouseLeftButtonDown(object sender, MouseButtonEventArgs e)
        {
            Focus();
            if (Scene == null || Scene.ActiveCamera == null || IsFullscreen)
                return;

            Point location = e.GetPosition(renderSurface);
            Rect rectangle = new Rect(0, 0, renderSurface.RenderSize.Width, renderSurface.RenderSize.Height);

            if (rectangle.Contains(location))
            {
                mouseCaptured = true;

                Scene.ControlManager.HandleMouseDown(new Vector2((float)location.X, (float)location.Y));
            }
        }

        private void UserControl_MouseLeftButtonUp(object sender, MouseButtonEventArgs e)
        {
            HandleMouseUp();
        }

        private void UserControl_MouseMove(object sender, MouseEventArgs e)
        {
            if (!IsCtrlKeyDown)
            {
                if (Scene == null || Scene.ActiveCamera == null || (!mouseCaptured && !IsFullscreen))
                    return;
                Point location = e.GetPosition(renderSurface);

                Scene.ControlManager.HandleMouseMove(new Vector2((float)location.X, (float)location.Y));
            }
        }

        bool IsCtrlKeyDown = false;
        private void UserControl_KeyDown(object sender, KeyEventArgs e)
        {
            lock (moves)
            {
                if (e.Key == Key.Ctrl)
                {
                    IsCtrlKeyDown = true;
                    return;
                }
                if (e.Key == Key.Left && !moves.Contains(MoveDirection.Left))
                    moves.Add(MoveDirection.Left);
                if (e.Key == Key.Right && !moves.Contains(MoveDirection.Right))
                    moves.Add(MoveDirection.Right);
                if (e.Key == Key.Up && !moves.Contains(MoveDirection.Forward))
                    moves.Add(MoveDirection.Forward);
                if (e.Key == Key.Down && !moves.Contains(MoveDirection.Backward))
                    moves.Add(MoveDirection.Backward);
            }
        }

        private void UserControl_MouseLeave(object sender, MouseEventArgs e)
        {
            HandleMouseUp();
        }

        private void UserControl_MouseEnter(object sender, MouseEventArgs e)
        {
            HandleMouseUp();
        }

        private void UserControl_KeyUp(object sender, KeyEventArgs e)
        {
            lock (moves)
            {
                if (e.Key == Key.Ctrl)
                {
                    IsCtrlKeyDown = false;
                    return;
                }

                if (e.Key == Key.Left)
                    moves.Remove(MoveDirection.Left);
                if (e.Key == Key.Right)
                    moves.Remove(MoveDirection.Right);
                if (e.Key == Key.Up)
                    moves.Remove(MoveDirection.Forward);
                if (e.Key == Key.Down)
                    moves.Remove(MoveDirection.Backward);
            }
        }

        public bool IsFullscreen
        {
            get { return isFullscreen; }
            set
            {
                if (value == isFullscreen)
                    return;
                if (value)
                {
                    CaptureMouse();
                    Cursor = Cursors.None;

                    isFullscreen = true;
                    Application.Current.Host.Content.IsFullScreen = true;
                }
                else
                {
                    if (Application.Current.Host.Content.IsFullScreen)
                        return;
                    ReleaseMouseCapture();
                    Cursor = Cursors.Arrow;
                    isFullscreen = false;
                    HandleMouseUp();
                }
            }
        }

        private void UserControl_Loaded(object sender, RoutedEventArgs e)
        {

        }
    }
}
