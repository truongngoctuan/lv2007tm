using System;

namespace Babylon
{
    public abstract class RootElement : IDisposable
    {
        public Guid ID
        {
            get;
            set;
        }

        public string Name
        {
            get;
            set;
        }

        internal RootElement(string name)
        {
            Name = name;
            ID = Guid.NewGuid();
        }

        public abstract void Dispose();
    }
}
