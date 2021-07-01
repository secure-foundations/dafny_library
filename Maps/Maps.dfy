module Maps {
  // converts a map to a sequence
  function method {:opaque} convert_map_to_seq<T>(n:int, m:map<int, T>): seq<T>
    requires n >= 0;
    requires forall i {:trigger i in m} :: 0 <= i < n ==> i in m;
    ensures |convert_map_to_seq(n, m)| == n;
    ensures var s := convert_map_to_seq(n, m);
    forall i {:trigger s[i]} :: 0 <= i < n ==> s[i] == m[i];
  {
      if n == 0 then []
      else convert_map_to_seq(n-1, m) + [m[n-1]]
  }
}
