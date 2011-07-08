namespace Babylon
{
    public partial class Engine
    {
        public StandardEffect StandardEffect { get; private set; }

        public PerPixelEffect PerPixelEffect { get; private set; }

        void PrepareEffects()
        {
            StandardEffect = new StandardEffect(this);
            PerPixelEffect = new PerPixelEffect(this);
        }
    }
}
