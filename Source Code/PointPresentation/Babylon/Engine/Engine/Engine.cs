using System.Collections.ObjectModel;
using System.Threading;
using System.Windows.Controls;
using Babylon.Toolbox;
using Microsoft.Xna.Framework.Graphics;
using System;
using Microsoft.Xna.Framework.Silverlight;

namespace Babylon
{
    public partial class Engine : IDisposable
    {
        readonly ObservableCollection<Scene> scenes = new ObservableCollection<Scene>();
        DrawEventArgs currentDrawEvent;
        int framesCounter;
        int framesTime;

        public ObservableCollection<Scene> Scenes
        {
            get { return scenes; }
        }

        //nhminh
        //internal GraphicsDevice Device { get; set; }
        public GraphicsDevice Device { get; set; }

        public int FPS { get; private set; }

        public int RenderWidth { get; internal set; }

        public int RenderHeight { get; internal set; }

        public bool DiffuseEnable { get; set; }
        public bool SpecularEnable { get; set; }
        public bool EmissiveEnable { get; set; }

        public bool AlphaTestEnable { get; set; }

        public float AspectRatio
        {
            get
            {
                return RenderWidth / (float)RenderHeight;
            }
        }

        internal StatesManager StatesManager { get; private set; }

        public SynchronizationContext SynchronizationContext { get; private set; }

        public Engine()
        {
            DiffuseEnable = true;
            SpecularEnable = true;
            EmissiveEnable = true;

            if (GraphicsDeviceManager.Current.RenderMode != RenderMode.Hardware)
            {
                switch (GraphicsDeviceManager.Current.RenderModeReason)
                {
                    case RenderModeReason.GPUAccelerationDisabled:
                        throw new Exception(Strings.NoGPUAcceleration);
                    case RenderModeReason.SecurityBlocked:
                        throw new Exception(Strings.HardwareAccelerationBlockedBySecurityReason);
                    case RenderModeReason.Not3DCapable:
                        throw new Exception(Strings.HardwareAccelerationNotAvailable);
                    case RenderModeReason.TemporarilyUnavailable:
                        throw new Exception(Strings.HardwareAccelerationNotAvailable);
                }
            }

            SynchronizationContext = SynchronizationContext.Current;
        }

        public void ResizeRenderZone(int renderWidth, int renderHeight)
        {
            RenderWidth = renderWidth;
            RenderHeight = renderHeight;
        }

        public void BeginFrame(DrawEventArgs eventArgs)
        {
            if (StatesManager == null)
            {
                StatesManager = new StatesManager(eventArgs.GraphicsDevice);
                PrepareEffects();
            }

            currentDrawEvent = eventArgs;

            framesCounter++;
            framesTime += (int)eventArgs.DeltaTime.TotalMilliseconds;
            if (framesTime >= 1000)
            {
                FPS = framesCounter;
                framesTime = 0;
                framesCounter = 0;
            }
        }

        public void EndFrame()
        {
            currentDrawEvent.InvalidateSurface();
        }
    }
}
