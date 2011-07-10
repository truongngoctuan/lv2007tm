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
            localRootStreamUri = Utils.Global.MakeRelativeUri(sceneUri, string.Format("{0}.streams", sceneName));

            Load(Utils.Global.GetLocalStream(sceneUri));
        }

        public void LoadPack(Uri sceneUri)
        {
            //LoadMode = Mode.Package;

            string sceneName = Path.GetFileNameWithoutExtension(sceneUri.ToString());
            localRootStreamUri = Utils.Global.MakeRelativeUri(sceneUri, string.Format("{0}.streams", sceneName));

            Load(Utils.Global.GetPackStream(sceneUri));
        }
    }
}
        