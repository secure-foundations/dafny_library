include "../NativeTypes.dfy"

module {:extern "IoNative"} Io {

  import opened NativeTypes

  class OkState
  {
    constructor {:extern} () requires false
    function {:extern} ok(): bool reads this
  }

  class HostEnvironment
  {
    ghost var ok: OkState
  }

  class FileStream
  {
    ghost var env: HostEnvironment
    function {:extern} Name(): string reads this
    function {:extern} IsOpen(): bool reads this
    constructor {:extern} () requires false

    static method {:extern} Open(name: array<char>, ghost env: HostEnvironment)
      returns (ok: bool, f: FileStream)
      requires env.ok.ok()
      modifies env.ok
      ensures  env.ok.ok() == ok
      ensures  ok ==> fresh(f) && f.env == env && f.IsOpen() && f.Name() == name[..]

    method {:extern} Close() returns (ok: bool)
      requires env.ok.ok()
      requires IsOpen()
      modifies this
      modifies env.ok
      ensures  env == old(env)
      ensures  env.ok.ok() == ok

    method {:extern} Read(fileOffset: nat32, buffer: array<uint8>, start: int32, end: int32) returns (ok: bool)
      requires env.ok.ok()
      requires IsOpen()
      requires 0 <= start as int <= end as int <= buffer.Length
      modifies this
      modifies env.ok
      modifies buffer
      ensures  env == old(env)
      ensures  env.ok.ok() == ok
      ensures  Name() == old(Name())
      ensures  forall i:int :: 0 <= i < buffer.Length && !(start as int <= i < end as int) ==> buffer[i] == old(buffer[i])
      ensures  ok ==> IsOpen()

    method {:extern} Write(fileOffset: nat32, buffer: array<uint8>, start: int32, end: int32) returns (ok: bool)
      requires env.ok.ok()
      requires IsOpen()
      requires 0 <= start as int <= end as int <= buffer.Length
      modifies this
      modifies env.ok
      ensures  env == old(env)
      ensures  env.ok.ok() == ok
      ensures  Name() == old(Name())
      ensures  ok ==> IsOpen()

    method {:extern} Flush() returns (ok: bool)
      requires env.ok.ok()
      requires IsOpen()
      modifies this
      modifies env.ok
      ensures  env == old(env)
      ensures  env.ok.ok() == ok
      ensures  Name() == old(Name())
      ensures  ok ==> IsOpen()
  }

}
