using System;
using System.Windows;
using System.Reflection;


namespace ShaderEffectsLibrary
{
    internal static class Global
    {
        public static Uri MakePackUri( string relativeFile )
        {
            string uriString = "/" + AssemblyShortName + ";component/" + relativeFile;
            return new Uri( uriString, UriKind.Relative );
        }

        private static string AssemblyShortName
        {
            get
            {
                if ( _assemblyShortName == null )
                {
                    Assembly a = typeof( Global ).Assembly;

                    // Pull out the short name.
                    _assemblyShortName = a.ToString().Split( ',' )[ 0 ];
                }

                return _assemblyShortName;
            }
        }

        private static string _assemblyShortName;
    }
}
