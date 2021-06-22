module {:extern} Options {
  newtype uint8 =  x | 0 <= x < 0x100
  newtype uint16 = x | 0 <= x < 0x1_0000
  newtype uint32 = x | 0 <= x < 0x1_0000_0000
  newtype uint64 = x | 0 <= x < 0x1_0000_0000_0000_0000

  newtype int8  = x | -0x80 <= x < 0x80
  newtype int16 = x | -0x8000 <= x < 0x80000
  newtype int32 = x | -0x8000_0000 <= x < 0x8000_0000
  newtype int64 = x | -0x8000_0000_0000_0000 <= x < 0x8000_0000_0000_0000

  datatype Option<T> = None | Some(value: T) {
    function method to_result(): Result<T> {
      match this
      case Some(v) => Success(v)
      case None() => Failure("Option is None")
    }
    
    function method unwrap_or(default: T): T {
      match this
      case Some(v) => v
      case None => default
    }
  }
  
  datatype Result<T> = | Success(value: T) | Failure(error: string) {
    function method to_option(): Option<T> {
      match this
      case Success(s) => Some(s)
      case Failure(e) => None()
    }
    function method unwrap_pr(default: T): T {
      match this
      case Success(s) => s
      case Failure(e) => default
    }
  }

  method to_array<T>(s: seq<T>) returns (a: array<T>)
    ensures fresh(a)
    ensures a.Length == |s|
    ensures forall i :: 0 <= i < |s| ==> a[i] == s[i]
  {
    a := new T[|s|](i requires 0 <= i < |s| => s[i]);
  }
} 