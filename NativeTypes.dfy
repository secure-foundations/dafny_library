module NativeTypes {

  newtype uint8 =  x | 0 <= x < 0x100
  newtype uint16 = x | 0 <= x < 0x1_0000
  newtype uint32 = x | 0 <= x < 0x1_0000_0000
  newtype uint64 = x | 0 <= x < 0x1_0000_0000_0000_0000

  newtype int8  = x | -0x80 <= x < 0x80
  newtype int16 = x | -0x8000 <= x < 0x80000
  newtype int32 = x | -0x8000_0000 <= x < 0x8000_0000
  newtype int64 = x | -0x8000_0000_0000_0000 <= x < 0x8000_0000_0000_0000
  
}