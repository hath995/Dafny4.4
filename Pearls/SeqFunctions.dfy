
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
}