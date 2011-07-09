using System;
using System.IO;

namespace _3DPresentation
{
    public partial class CustomScene : Babylon.Scene
    {
        private void PrepareIO()
        {
        }

        public override void LoadLocal(Uri sceneUri)
        {
            LoadMode = Mode.Local;

            string sceneName = Path.GetFileNameWithoutExtension(sceneUri.ToString());
            localRootStreamUri = Utils.Global.MakePackUri(sceneUri, string.Format("{0}.streams", sceneName));

            Load(Utils.Global.GetStream(sceneUri));
        }        
    }
}
        