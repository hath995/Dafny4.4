
module SeqFunctions {

    function Map<T,R>(f: (T -> R), xs: seq<T>): (result: seq<R>)
        ensures |result| == |xs|
        // ensures forall i {:trigger result[i]} :: 0 <= i < |xs| ==> result[i] == f(xs[i])
        ensures forall i :: 0 <= i < |xs| ==> result[i] == f(xs[i])
    {
        if |xs| == 0 then []
        else [f(xs[0])] + Map(f, xs[1..])
    }

    lemma LemmaMapDistributesOverConcat<T,R>(f: (T -> R), xs: seq<T>, ys: seq<T>)
        ensures Map(f, xs + ys) == Map(f, xs) + Map(f, ys)
    {
        reveal Map();
        if |xs| == 0 {
        assert xs + ys == ys;
        } else {
        calc {
            Map(f, xs + ys);
            { assert (xs + ys)[0] == xs[0]; assert (xs + ys)[1..] == xs[1..] + ys; }
            Map(f, [xs[0]]) + Map(f, xs[1..] + ys);
            Map(f, [xs[0]]) + Map(f, xs[1..]) + Map(f, ys);
            {assert [(xs + ys)[0]] + xs[1..] + ys == xs + ys;}
            Map(f, xs) + Map(f, ys);
        }
        }
    }

function Filter<T>(f: (T -> bool), xs: seq<T>): (result: seq<T>)
    ensures |result| <= |xs|
    ensures forall i: nat :: i < |result| ==> f(result[i])
  {
    if |xs| == 0 then []
    else (if f(xs[0]) then [xs[0]] else []) + Filter(f, xs[1..])
  }

  lemma FilterHas<T>(f: T-> bool, xs: seq<T>, x: T)
    requires x in xs
    requires f(x)
    ensures x in Filter(f, xs)
  {}

  /* Filtering a sequence is distributive over concatenation. That is, concatenating two sequences 
     and then using "Filter" is the same as using "Filter" on each sequence separately, and then 
     concatenating the two resulting sequences. */
  lemma LemmaFilterDistributesOverConcat<T(!new)>(f: (T -> bool), xs: seq<T>, ys: seq<T>)
    ensures Filter(f, xs + ys) == Filter(f, xs) + Filter(f, ys)
  {
    reveal Filter();
    if |xs| == 0 {
      assert xs + ys == ys;
    } else {
      calc {
        Filter(f, xs + ys);
        { assert {:split_here} (xs + ys)[0] == xs[0]; assert (xs + ys)[1..] == xs[1..] + ys; }
        Filter(f, [xs[0]]) + Filter(f, xs[1..] + ys);
        { assert Filter(f, xs[1..] + ys) == Filter(f, xs[1..]) + Filter(f, ys); }
        Filter(f, [xs[0]]) + (Filter(f, xs[1..]) + Filter(f, ys));
        { assert {:split_here} [(xs + ys)[0]] + (xs[1..] + ys) == xs + ys; }
        Filter(f, xs) + Filter(f, ys);
      }
    }
  } 

  function Conj<T>(f: (T -> bool), g: (T -> bool)): (T-> bool) {
    x => f(x) && g(x)
  }

  lemma LemmaFilterDistributesOverAnd<T(!new)>(f: (T -> bool), g: (T -> bool), xs: seq<T>)
    ensures Filter(Conj(f,g), xs) == Filter(f, Filter(g, xs))
  {
    if xs == [] {

        assert Filter(Conj(f,g), xs) == Filter(f, Filter(g, xs));
    } else if |xs| == 1 {

        assert Filter(Conj(f,g), xs) == Filter(f, Filter(g, xs));
    }else {
        var x := xs[0];
        var tail := xs[1..];
        assert xs == [xs[0]] + xs[1..];
        LemmaFilterDistributesOverAnd(f,g, xs[1..]);
        var inner_g_x := Filter(g, [x]);
        if(f(x) && g(x)) {

            assert Filter(Conj(f,g), xs) == Filter(f, Filter(g, xs));
        }else{
            LemmaFilterDistributesOverConcat(Conj(f,g), [xs[0]], xs[1..]);
            assert Filter(Conj(f,g), [xs[0]]) == [];
            assert Filter(f, Filter(g, [xs[0]])) == [];
            assert Filter(f, Filter(g, xs[1..])) == Filter(Conj(f, g), xs[1..]);
            LemmaFilterDistributesOverConcat(g, [x], tail);

            if !f(x) {
                LemmaFilterDistributesOverConcat(f, inner_g_x, Filter(g, tail));
                assert Filter(Conj(f,g), xs) == Filter(f, Filter(g, xs));
            }else{
                assert !g(x);
                assert inner_g_x == [];
                assert [] + Filter(g, tail) == Filter(g, tail);
                assert Filter(Conj(f,g), xs) == Filter(f, Filter(g, xs));
            }
            assert Filter(Conj(f,g), xs) == Filter(f, Filter(g, xs));
        }
        assert Filter(Conj(f,g), xs) == Filter(f, Filter(g, xs));
    }
  }

  lemma FilteredInXS<T(!new)>(f: T -> bool, xs: seq<T>)
    ensures forall xx :: xx in Filter(f, xs) ==> xx in xs
  {}

  lemma FilterTargets<T(!new)>(f: T -> bool, xs: seq<T>)
    requires |Filter(f, xs)| > 1
    ensures exists i,j, m,n :: i != j && 0 <= i < j < |Filter(f, xs)| && m != n && 0 <= m < n < |xs| && f(xs[m]) && xs[m] == Filter(f, xs)[i] && f(xs[n]) && xs[n] == Filter(f, xs)[j]
  {
    assert |xs| >= |Filter(f, xs)|;
    assert xs == [xs[0]]+xs[1..];
    assert xs == [xs[0]]+[xs[1]]+xs[2..];
    assert xs[1..][1..] == xs[2..];
    // FilteredInXS(f, xs);
    FilteredInXS(f, xs[1..]);
    FilteredInXS(f, xs[2..]);
    if |Filter(f, xs)| == 2 {
      assert Filter(f,xs)[0] in xs;
      assert Filter(f,xs)[1] in xs;
      if f(xs[0]) {
        calc {
          Filter(f, xs);
          [xs[0]]+Filter(f, xs[1..]);
        }
        assert Filter(f,xs)[1] in Filter(f, xs[1..]);
        assert Filter(f, xs)[0] == xs[0];
        assert Filter(f,xs)[1] in Filter(f, xs[1..]);
        var j :| 0 <= j < |xs[1..]|  && Filter(f, xs)[1] == xs[1..][j];
        assert Filter(f, xs)[1] == xs[j+1];
      }else if f(xs[1]) {
        assert Filter(f, xs)[0] == xs[1];
        calc {
          Filter(f, xs);
          [] + Filter(f, xs[1..]);
          [xs[1]]+Filter(f, xs[1..][1..]);
          [xs[1]]+Filter(f, xs[2..]);
        }
        assert Filter(f,xs)[1] in Filter(f, xs[2..]);
        var j :| 0 <= j < |xs[2..]|  && Filter(f, xs)[1] == xs[2..][j];
        assert Filter(f, xs)[1] == xs[j+2];
      }else{
        FilterTargets(f, xs[2..]);
      }
    }else{
      // FilterTargets(f, xs[1..]);
      if f(xs[0]) {
        assert Filter(f, xs)[0] == xs[0];
        calc {
          Filter(f, xs);
          [xs[0]]+Filter(f, xs[1..]);
        }
        assert Filter(f,xs)[1] in Filter(f, xs[1..]);
        var j :| 0 <= j < |xs[1..]|  && Filter(f, xs)[1] == xs[1..][j];
        assert Filter(f, xs)[1] == xs[j+1];
      }else if f(xs[1]) {
        calc {
          Filter(f, xs);
          [] + Filter(f, xs[1..]);
          [xs[1]]+Filter(f, xs[1..][1..]);
          [xs[1]]+Filter(f, xs[2..]);
        }
        assert Filter(f, xs)[0] == xs[1];
        assert Filter(f,xs)[1] in Filter(f, xs[2..]);
        var j :| 0 <= j < |xs[2..]|  && Filter(f, xs)[1] == xs[2..][j];
        assert Filter(f, xs)[1] == xs[j+2];
      }else{
        calc {
          Filter(f, xs);
          [] + Filter(f, xs[1..]);
          [] + [] + Filter(f, xs[1..][1..]);
        }
        FilterTargets(f, xs[2..]);

      }
    }
  }

  // lemma FilterTargeted<T(!new)(==)>(f: T->bool, xs: seq<T>, i: nat, j: nat)
  //   requires |Filter(f, xs)| > 1
  //   requires i < j < |Filter(f, xs)|
  //   ensures exists m,n :: m != n && 0 <= m < n < |xs| && Filter(f,xs)[i] == xs[m] && Filter(f, xs)[j] == xs[n] 
  // {
  //   // FilterTargets(f, xs);
  //   assert |xs| >= |Filter(f, xs)|;
  //   assert xs == [xs[0]]+xs[1..];
  //   assert xs == [xs[0]]+[xs[1]]+xs[2..];
  //   assert xs[1..][1..] == xs[2..];
  //   FilteredInXS(f, xs);
  //   FilteredInXS(f, xs[1..]);
  //   FilteredInXS(f, xs[2..]);

  //   if |Filter(f, xs)| == 2 {
  //     assert Filter(f,xs)[0] in xs;
  //     assert Filter(f,xs)[1] in xs;
  //     assert i == 0;
  //     assert j == 1;
  //     if f(xs[0]) {
  //       calc {
  //         Filter(f, xs);
  //         [xs[0]]+Filter(f, xs[1..]);
  //       }
  //       assert Filter(f,xs)[1] in Filter(f, xs[1..]);
  //       assert Filter(f, xs)[0] == xs[0];
  //       assert Filter(f,xs)[1] in Filter(f, xs[1..]);
  //       var n :| 0 <= n < |xs[1..]|  && Filter(f, xs)[1] == xs[1..][n];
  //       assert Filter(f, xs)[1] == xs[n+1];
  //     }else if f(xs[1]) {
  //       assert Filter(f, xs)[0] == xs[1];
  //       calc {
  //         Filter(f, xs);
  //         [] + Filter(f, xs[1..]);
  //         [xs[1]]+Filter(f, xs[1..][1..]);
  //         [xs[1]]+Filter(f, xs[2..]);
  //       }
  //       assert Filter(f,xs)[1] in Filter(f, xs[2..]);
  //       var n :| 0 <= n < |xs[2..]|  && Filter(f, xs)[1] == xs[2..][n];
  //       assert Filter(f, xs)[1] == xs[n+2];
  //     }else{
  //       FilterTargeted(f, xs[2..], i,j);
  //     }
  //   }else{
  //     var fs := Filter(f, xs);
  //     if i == 0 {

  //     }else{

  //     }
  //     // FilterTargets(f, xs[1..]);
  //     // if f(xs[0]) {
  //     //   assert Filter(f, xs)[0] == xs[0];
  //     //   calc {
  //     //     Filter(f, xs);
  //     //     [xs[0]]+Filter(f, xs[1..]);
  //     //   }
  //     //   assert Filter(f,xs)[1] in Filter(f, xs[1..]);
  //     //   var n :| 0 <= n < |xs[1..]|  && Filter(f, xs)[1] == xs[1..][n];
  //     //   assert Filter(f, xs)[1] == xs[n+1];
  //     // }else if f(xs[1]) {
  //     //   calc {
  //     //     Filter(f, xs);
  //     //     [] + Filter(f, xs[1..]);
  //     //     [xs[1]]+Filter(f, xs[1..][1..]);
  //     //     [xs[1]]+Filter(f, xs[2..]);
  //     //   }
  //     //   assert Filter(f, xs)[0] == xs[1];
  //     //   assert Filter(f,xs)[1] in Filter(f, xs[2..]);
  //     //   var n :| 0 <= n < |xs[2..]|  && Filter(f, xs)[1] == xs[2..][n];
  //     //   assert Filter(f, xs)[1] == xs[n+2];
  //     // }else{
  //     //   calc {
  //     //     Filter(f, xs);
  //     //     [] + Filter(f, xs[1..]);
  //     //     [] + [] + Filter(f, xs[1..][1..]);
  //     //   }
  //     //   FilterTargeted(f, xs[2..], i,j);

  //     // }
  //   }
    
  // }

   function FoldRight<A, T>(f: (T, A) -> A, xs: seq<T>, init: A): A
  {
    if |xs| == 0 then init
    else f(xs[0], FoldRight(f, xs[1..], init))
  }

  lemma LemmaFoldRightDistributesOverConcat<A, T>(f: (T, A) -> A, init: A, xs: seq<T>, ys: seq<T>)
    ensures FoldRight(f, xs + ys, init) == FoldRight(f, xs, FoldRight(f, ys, init))
  {
    if |xs| == 0 {
      assert xs + ys == ys;
    } else {
      calc {
        FoldRight(f, xs, FoldRight(f, ys, init));
        f(xs[0], FoldRight(f, xs[1..], FoldRight(f, ys, init)));
        f(xs[0], FoldRight(f, xs[1..] + ys, init));
        { assert (xs + ys)[0] == xs[0];
          assert (xs +ys)[1..] == xs[1..] + ys; }
        FoldRight(f, xs + ys, init);
      }
    }
  }
}