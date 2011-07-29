using System;
using System.IO;
using System.Net;

namespace Babylon
{
    public partial class Scene
    {
        Uri rootStreamUri;

        public int ItemsToStream { get; internal set; }

        //nhminh
        protected virtual void GetPackDataStream(IStreamableData data)
        {
            throw new NotImplementedException();
        }

        //nhminh
        protected virtual void GetLocalDataStream(IStreamableData data)
        {
            throw new NotImplementedException();
        }
        
        void GetDataStream(IStreamableData data)
        {
            //nhminh
            if (LoadMode == Mode.Local)
            {
                GetLocalDataStream(data);
                return;
            }
            else if (LoadMode == Mode.Package)
            {
                GetPackDataStream(data);
                return;
            }
            //end nhminh

            HttpWebRequest webRequest = (HttpWebRequest)WebRequest.Create(new Uri(rootStreamUri + "/" + data.StreamID + ".bsfstream"));

            //nhminh
            //if(!Logger.IsInitialized)
            //   Logger.Init();
            //Logger.Write(rootStreamUri + "/" + data.StreamID + ".bsfstream");
            //end nhminh

            webRequest.BeginGetResponse(asyncResult =>
                                            {
                                                WebResponse response = webRequest.EndGetResponse(asyncResult);
                                                using (Stream stream = response.GetResponseStream())
                                                {
                                                    data.ProcessStream(stream);

                                                    lock (this)
                                                    {
                                                        ItemsToStream--;
                                                        //nhminh
                                                        //if (ItemsToStream == 0)
                                                        //    Logger.End();
                                                        //end nhminh
                                                    }
                                                }
                                            }, null);
        }

        internal void RegisterForStreaming(IStreamableData data)
        {
            engine.SynchronizationContext.Post(o =>
                                             {
                                                 lock (data)
                                                 {
                                                     if (data.StreamingState != StreamingState.PreLoaded)
                                                         return;

                                                     data.StreamingState = StreamingState.Loading;
                                                 }

                                                 GetDataStream(data);
                                             }, null);
        }
    }
}
