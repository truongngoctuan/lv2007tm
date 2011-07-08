using System.IO;

namespace Babylon
{
    public interface IStreamableData
    {
        StreamingState StreamingState { get; set; }
        int StreamID { get; }

        void ProcessStream(Stream stream);
    }
}
