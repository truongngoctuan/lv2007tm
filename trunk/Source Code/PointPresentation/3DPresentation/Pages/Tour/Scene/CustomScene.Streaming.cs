using System;
using System.IO;

namespace _3DPresentation
{
    public partial class CustomScene : Babylon.Scene
    {
        private void PrepareStreaming()
        {
        }

        Uri localRootStreamUri;
        protected override void GetLocalDataStream(Babylon.IStreamableData data)
        {
            Uri uri = new Uri(localRootStreamUri + "/" + data.StreamID + ".bsfstream", UriKind.Relative);
            Stream stream = Utils.Global.GetStream(uri);
            data.ProcessStream(stream);
        }
    }
}
        