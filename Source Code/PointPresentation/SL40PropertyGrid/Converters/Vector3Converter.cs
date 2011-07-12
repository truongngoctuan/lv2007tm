using System;
using System.ComponentModel;
using System.Globalization;

namespace SL40PropertyGrid.Converters
{
	public class Vector3Converter : TypeConverter
	{
		// Methods
		public override bool CanConvertFrom(ITypeDescriptorContext context, Type sourceType)
		{
			return ((sourceType == typeof(string)) || base.CanConvertFrom(context, sourceType));
		}

		public override object ConvertFrom(ITypeDescriptorContext context, CultureInfo culture, object value)
		{
			if (value is string)
			{
				string s = ((string)value).Trim();
                string[] items = s.Split(new string[] { " ", "{X:" , "Y:" , "Z:", "}" }, StringSplitOptions.RemoveEmptyEntries);
				try
				{                    
                    int nFloats = 0;
                    float[] arrFloats = new float[items.Length];
                    for (int i = 0; i < items.Length; i++)
                    {
                        float single;
                        if (float.TryParse(items[i], out single))
                        {
                            arrFloats[nFloats++] = single;
                        }
                    }
                    if (nFloats == 3)
                    {
                        Microsoft.Xna.Framework.Vector3 vector3 = new Microsoft.Xna.Framework.Vector3(arrFloats[0], arrFloats[1], arrFloats[2]);
                        arrFloats = null;
                        return vector3;
                    }
                    arrFloats = null;
				}
				catch (FormatException)
				{
					throw new FormatException();
				}
			}
			return base.ConvertFrom(context, culture, value);
		}
	}
}
