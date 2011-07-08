using Babylon.Maths;
using Microsoft.Xna.Framework;

namespace Babylon
{
    public class Targetable : RootElement
    {
        protected Vector3 position;

        public virtual Vector3 Position
        {
            get
            {
                return position;
            }
            set
            {
                position = value;
            }
        }       

        public Targetable(string name) : base(name)
        {

        }

        public override void Dispose()
        {
        }
    }
}
