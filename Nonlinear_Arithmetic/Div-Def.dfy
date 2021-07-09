//- Specs/implements mathematical div and mod, not the C version.
//- This may produce "surprising" results for negative values
//- For example, -3 div 5 is -1 and -3 mod 5 is 2.
//- Note this is consistent: -3 * -1 + 2 == 5

module DivDef {

  function method div(x: int, d: int): int
    requires d != 0
  {
    x / d
  }

  function method mod(x: int, d: int): int
    requires d != 0
  {
    x % d
  }

  function method div_recursive(x: int, d: int): int
    requires d != 0
  {
    if d > 0 then
      div_pos(x, d)
    else
      -1 * div_pos(x, -1*d)
  }

  function method mod_recursive(x: int, d: int): int
    requires d > 0
    decreases if x < 0 then (d - x) else x
  {
    if x < 0 then
      mod_recursive(d + x, d)
    else if x < d then
      x
    else
      mod_recursive(x - d, d)
  }

  function method div_pos(x:int, d:int) : int
    requires d >  0
    decreases if x < 0 then (d - x) else x
  {
    if x < 0 then
      -1 + div_pos(x+d, d)
    else if x < d then
      0
    else
      1 + div_pos(x-d, d)
  }

}
