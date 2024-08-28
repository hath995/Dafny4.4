module Change {
  function sum(ns: seq<nat>): nat
  {
    if |ns| == 0 then
      0
    else
      ns[0] + sum(ns[1..])
  }

  lemma sumConcat(xs: seq<nat>, ys: seq<nat>) 
      ensures sum(xs) + sum(ys) == sum(xs + ys)
  {
      if xs == [] {
          assert xs + ys == ys;
          assert sum(xs) == 0;
          assert sum(xs) + sum(ys) == sum(xs + ys);
      }else {
          assert xs == [xs[0]] + xs[1..];
          assert xs + ys == [xs[0]] + xs[1..]+ys;
          sumConcat(xs[1..] , ys);
          assert sum([xs[0]]) == xs[0];
          assert (xs+ys)[1..] == xs[1..]+ys;
          assert sum(xs) + sum(ys) == sum(xs + ys);
      }
  }

  method Change(amount: nat)
    returns (result: seq<nat>)
    requires amount >= 8
    ensures forall i :: 0 <= i <= |result| - 1 ==> result[i] == 3 || result[i] == 5
    ensures sum(result) == amount
  {
    if amount == 8 {
      result := [3, 5];
      assert sum(result) == amount;
    } else if amount == 9 {
      result := [3, 3, 3 ];
      assert sum(result) == amount;
    } else if amount == 10 {
      result := [5, 5];
      assert sum(result) == amount;
    } else {
      var tmp := Change(amount - 3);
      assert sum(tmp) == amount - 3;
      var x := [3];
      assert sum(x) == 3;
      result :=  tmp + x;
      sumConcat(tmp, x);
      assert sum(x) + sum(tmp) == sum(result);
    }
  }
}