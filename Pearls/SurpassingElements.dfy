include "./SeqFunctions.dfy"
module SurpassingProblem {
  import opened SeqFunctions
  function Tails<T>(xs: seq<T>): seq<seq<T>>
    ensures forall xxs :: xxs in Tails(xs) ==> |xs| > 0
  {
    if xs == [] then
      []
    else
      [xs]+Tails(xs[1..])
  }

  lemma TailsHas<T(==)>(xs: seq<T>, i: nat)
    requires 0 <= i < |xs|
    ensures xs[i..] in Tails(xs)
  {
    if i == 0 {

    }else{
      // assert xs[]
      TailsHas(xs[1..], i-1);

    }
  }

  lemma TailsHasAllSlices<T(==)>(xs: seq<T>)
    ensures forall i :: 0 <= i < |xs| ==> xs[i..] in Tails(xs)
  {

    forall i | 0 <= i < |xs|
      ensures xs[i..] in Tails(xs)
    {
      TailsHas(xs,i);
    }
  }

  function scount<T>(x: T, xs: seq<T>, cpm: (T,T) -> bool): nat {
    |Filter(y => cpm(x,y) ,xs)|
  }

  lemma ScountHasLarger<T>(x: T, xs: seq<T>, cpm: (T,T) -> bool)
    ensures forall z :: z in Filter(y => cpm(x, y), xs) ==> cpm(x, z)
  {}

  lemma LemmaTailsConcat<T>(xs: seq<T>, ys: seq<T>)
    ensures Tails(xs+ys) == Map(xxs => xxs+ys, Tails(xs))+Tails(ys)
  {
    if xs == [] {
      assert xs+ys == ys;
      assert Tails(xs) == [];

      assert Tails(xs+ys) == Map(xxs => xxs+ys,Tails(xs))+Tails(ys);
    }else if |xs| == 1 {

      assert Tails(xs+ys) == Map(xxs => xxs+ys,Tails(xs))+Tails(ys);
    }else{
      assert xs==[xs[0]]+xs[1..];
      assert (xs+ys)[1..] == xs[1..]+ys;
      LemmaTailsConcat(xs[1..], ys);

      assert Tails(xs+ys) == Map(xxs => xxs+ys,Tails(xs))+Tails(ys);
    }
  }

  lemma LemmaScountConcat<T>(xs: seq<T>, ys: seq<T>, z: T, cmp: (T,T) -> bool)
    ensures scount(z, xs+ys, cmp) == scount(z,xs,cmp) + scount(z,ys,cmp)
  {
    if xs == [] {
      assert xs+ys == ys;
      assert scount(z, xs+ys, cmp) == scount(z,xs,cmp) + scount(z,ys,cmp);
    }else if |xs| == 1 {
      assert scount(z, xs+ys, cmp) == scount(z,xs,cmp) + scount(z,ys,cmp);
    }else{
      assert xs==[xs[0]]+xs[1..];
      assert (xs+ys)[1..] == xs[1..]+ys;
      LemmaScountConcat(xs[1..], ys, z, cmp);

      assert scount(z, xs+ys, cmp) == scount(z,xs,cmp) + scount(z,ys,cmp);
    }
  }

  function maxNat(m: nat, a: nat): nat {
    if a > m then a else m
  }

  function maximum(xs: seq<nat>): nat
    requires |xs| > 0
  {
    FoldRight(maxNat, xs, xs[0])
  }

  lemma LemmaMaximumOne(xs: seq<nat>)
    requires |xs| == 1
    ensures maximum(xs) == xs[0]
  {
    calc{
      maximum(xs);
      FoldRight(maxNat, xs, xs[0]);
      maxNat(xs[0], FoldRight(maxNat, xs[1..], xs[0]));
      maxNat(xs[0], FoldRight(maxNat, [], xs[0]));
      maxNat(xs[0], xs[0]);
      xs[0];
    }
  }

    lemma LemmaFoldRightMaxOrInit(xs: seq<nat>, init: nat)
    ensures FoldRight(maxNat, xs, init) == init || FoldRight(maxNat, xs, init) in xs
  {
    if |xs| == 0 {
    } else {
      LemmaFoldRightMaxOrInit(xs[1..], init);
      
    }
  }

   lemma LemmaMaximumIn(xs: seq<nat>)
    requires |xs| > 0
    ensures maximum(xs) in xs
  {
    if |xs| == 1 {
      calc {
        maximum(xs);
        FoldRight(maxNat, xs, xs[0]);
        maxNat(xs[0], FoldRight(maxNat, [], xs[0]));
        maxNat(xs[0], xs[0]);
        xs[0];
      }
      assert maximum(xs) in xs;
    } else {
      assert maximum(xs) == FoldRight(maxNat, xs, xs[0]);
      LemmaFoldRightMaxOrInit(xs, xs[0]);
    }
  }

  lemma LemmaFoldRightMax(xs: seq<nat>, init: nat)
    ensures forall x :: x in xs ||x in {init} ==> FoldRight(maxNat, xs, init) >= x
  {
    if xs == [] {

    }else if |xs| == 1 {

    }else{
      assert xs == [xs[0]] + xs[1..];

    }
  }

  lemma LemmaMaximum(xs: seq<nat>)
    requires |xs| > 0
    ensures forall x:: x in xs ==> maximum(xs) >= x
  {
    if |xs| == 1{

    }else{
      LemmaFoldRightMax(xs, xs[0]);
    }
  }

 lemma LemmaFoldRightMaxAssoc(xs: seq<nat>, init: nat)
    requires |xs| > 0
    ensures FoldRight(maxNat, xs, init) == maxNat(maximum(xs), init)
  {
    if |xs| == 1 {
      // Base case: [x]. FoldRight result is max(x, init). maximum is x.

      calc {
        maximum(xs);
        // Definition
        FoldRight(maxNat, xs, xs[0]);
        // Unroll recursive step: f(head, FoldRight(tail, init))
        maxNat(xs[0], FoldRight(maxNat, [], xs[0]));
        // Unroll base case: FoldRight([], init) == init
        maxNat(xs[0], xs[0]);
        // Property of Max
        xs[0];
      }

    } else {
      // Inductive step: xs = [x] + tail
      // 1. Unroll FoldRight definition
      assert FoldRight(maxNat, xs, init) == maxNat(xs[0], FoldRight(maxNat, xs[1..], init));
      
      // 2. Apply IH to tail
      LemmaFoldRightMaxAssoc(xs[1..], init);
      // Now we have: maxNat(xs[0], maxNat(maximum(xs[1..]), init))
      
      // 3. Apply IH to definition of maximum(xs) to simplify it
      // maximum(xs) == FoldRight(..., xs[0])
      LemmaFoldRightMaxAssoc(xs[1..], xs[0]);
      // maximum(xs) == maxNat(xs[0], maximum(xs[1..]))
      
      // 4. Associativity/Commutativity logic (automatically handled by Dafny for maxNat)
      // max(a, max(b, c)) == max(max(a, b), c)
    }
  }

  lemma LemmaMaximumConcat(xs: seq<nat>, ys: seq<nat>)
    requires |ys| > 0
    requires |xs| > 0
    ensures maximum(xs+ys) == maxNat(maximum(xs), maximum(ys))
  {
    calc {
      maximum(xs + ys);
      // 1. Expand definition
      FoldRight(maxNat, xs + ys, (xs + ys)[0]);
      { assert (xs + ys)[0] == xs[0]; }
      FoldRight(maxNat, xs + ys, xs[0]);
      
      // 2. Distribute over concat (using your previous lemma)
      { LemmaFoldRightDistributesOverConcat(maxNat, xs[0], xs, ys); }
      FoldRight(maxNat, xs, FoldRight(maxNat, ys, xs[0]));
      
      // 3. Use Helper on the inner part (ys) to decouple xs[0]
      { LemmaFoldRightMaxAssoc(ys, xs[0]); }
      FoldRight(maxNat, xs, maxNat(maximum(ys), xs[0]));
      
      // 4. Use Helper on the outer part (xs)
      { LemmaFoldRightMaxAssoc(xs, maxNat(maximum(ys), xs[0])); }
      maxNat(maximum(xs), maxNat(maximum(ys), xs[0]));
      
      // 5. Associativity and Simplification
      // max(A, max(B, C)) == max(max(A, C), B)
      maxNat(maxNat(maximum(xs), xs[0]), maximum(ys));
      
      // 6. Observe that max(maximum(xs), xs[0]) is just maximum(xs)
      // (Because xs[0] is already contained in maximum(xs))
      { 
         LemmaFoldRightMaxAssoc(xs, xs[0]); 
         // This implies maximum(xs) == maxNat(maximum(xs), xs[0])
      }
      maxNat(maximum(xs), maximum(ys));
    }
  }

  predicate lt(a: int, b: int) {
    a < b
  }


  ghost function maxScount(xs: seq<int>): nat
    requires |xs| > 0
  {
    ThereIsAMaxScount(xs);
    var m :| 0 <= m < |xs| && forall i :: 0 <= i < |xs| ==> scount(xs[m..][0], xs[m..][1..], lt) >= scount(xs[i..][0], xs[i..][1..], lt);
    scount(xs[m..][0], xs[m..][1..], lt)
  }

  lemma LemmaMaxScountEquivalence(xs: seq<int>, m: nat, n: nat)
    requires 0 <= m < |xs| && forall i :: 0 <= i < |xs| ==> scount(xs[m..][0], xs[m..][1..], lt) >= scount(xs[i..][0], xs[i..][1..], lt)
    requires 0 <= n < |xs| && forall i :: 0 <= i < |xs| ==> scount(xs[n..][0], xs[n..][1..], lt) >= scount(xs[i..][0], xs[i..][1..], lt)
    ensures scount(xs[m..][0], xs[m..][1..], lt) == scount(xs[n..][0], xs[n..][1..], lt)
  {

  }

  function mscMapper(zs: seq<int>): nat
    // requires |zs| > 0
  {
    assume |zs| > 0;
    scount(zs[0], zs[1..], lt)
  } 

  function msc(xs: seq<int>): nat
    requires |xs| > 0
  {
    var zzs := Map(mscMapper, Tails(xs));
    maximum(zzs)
  }

  function Score(xs: seq<int>): nat requires |xs| > 0 { scount(xs[0], xs[1..], (a,b) => a < b) }

  lemma mscIsMaximum(xs: seq<int>)
    requires |xs| > 0
    ensures msc(xs) == maxScount(xs)
  {
    if |xs| == 1 {
      assert xs[1..] == [];
      assert Tails(xs) == [xs] + Tails(xs[1..]);
      assert Tails(xs) == [xs];
      assert Filter(xxs => |xxs| > 0, Tails(xs)) == [xs];
      assert scount(xs[0..][0], xs[0..][1..], lt) == scount(xs[0], xs[1..], lt);
      ThereIsAMaxScount(xs);
      var m :| 0 <= m < |xs| && forall i :: 0 <= i < |xs| ==> scount(xs[m..][0], xs[m..][1..], lt) >= scount(xs[i..][0], xs[i..][1..], lt);
      assert m == 0;
      var zzs := Map(mscMapper, Tails(xs));
      calc {
        Map(mscMapper, Tails(xs));
        Map(mscMapper, [xs]);
        [mscMapper(xs)]+Map(mscMapper, [xs][1..]);
        [mscMapper(xs)]+Map(mscMapper, []);
      }
      assert zzs == [scount(xs[0], xs[1..], lt)];
      calc {
        maximum(zzs);
        FoldRight(maxNat, zzs, zzs[0]);
        maxNat(zzs[0], FoldRight(maxNat, zzs[1..], zzs[0]));
        maxNat(zzs[0], FoldRight(maxNat, [], zzs[0]));
        maxNat(zzs[0], zzs[0]);
        zzs[0];
      }
      assert msc(xs) == scount(xs[0], xs[1..], lt);
      assert msc(xs) == maxScount(xs);
    }else{
      mscIsMaximum(xs[1..]);
      assert xs == [xs[0]]+xs[1..];
      assert Tails(xs) == [xs] + Tails(xs[1..]);
      calc {
        msc(xs);
        maximum(Map(mscMapper, Tails(xs)));
        maximum(Map(mscMapper, [xs] + Tails(xs[1..])));
        maximum([mscMapper(xs)]+Map(mscMapper,Tails(xs[1..])));
        {LemmaMaximumConcat([mscMapper(xs)],Map(mscMapper,Tails(xs[1..])));}
        maxNat(maximum([mscMapper(xs)]),maximum(Map(mscMapper,Tails(xs[1..]))));
        maxNat(maximum([mscMapper(xs)]),msc(xs[1..]));
        {LemmaMaximumOne([mscMapper(xs)]);}
        maxNat(mscMapper(xs),msc(xs[1..]));

      }
      ThereIsAMaxScount(xs);
      ThereIsAMaxScount(xs[1..]);
      LemmaMaximum(Map(mscMapper, Tails(xs)));
      var m :| 0 <= m < |xs| && forall i :: 0 <= i < |xs| ==> scount(xs[m..][0], xs[m..][1..], lt) >= scount(xs[i..][0], xs[i..][1..], lt);
      var m' :| 0 <= m' < |xs| && forall i :: 0 <= i < |xs| ==> scount(xs[m'..][0], xs[m'..][1..], lt) >= scount(xs[i..][0], xs[i..][1..], lt) && maxScount(xs) == scount(xs[m'..][0], xs[m'..][1..], lt);
      LemmaMaxScountEquivalence(xs, m, m');
      LemmaMaximum(Map(mscMapper, Tails(xs[1..])));
      var n :| 0 <= n < |xs[1..]| && forall i :: 0 <= i < |xs[1..]| ==> scount(xs[1..][n..][0], xs[1..][n..][1..], lt) >= scount(xs[1..][i..][0], xs[1..][i..][1..], lt) && maxScount(xs[1..]) == scount(xs[1..][n..][0], xs[1..][n..][1..], lt);
      assert msc(xs[1..]) == maxScount(xs[1..]);
      assert maxScount(xs[1..]) == scount(xs[1..][n..][0], xs[1..][n..][1..], lt);
      if mscMapper(xs) > msc(xs[1..]) {
        assert msc(xs) == mscMapper(xs);
        assert m == 0 by {
          if m != 0 {
            assert scount(xs[m..][0], xs[m..][1..], lt) == scount(xs[1..][m-1..][0], xs[1..][m-1..][1..], lt);
            assert scount(xs[m..][0], xs[m..][1..], lt) <= scount(xs[1..][n..][0], xs[1..][n..][1..], lt);
            assert mscMapper(xs) == scount(xs[0..][0], xs[0..][1..], lt);
            assert mscMapper(xs) > scount(xs[1..][n..][0], xs[1..][n..][1..], lt);
            assert false;
          }
        }
        assert msc(xs) == maxScount(xs);
      }else{
        assert msc(xs) == msc(xs[1..]);
        assert scount(xs[1..][n..][0], xs[1..][n..][1..], lt) == scount(xs[n+1..][0], xs[n+1..][1..], lt);
        forall i | 0 <= i < |xs| 
          ensures scount(xs[n+1..][0], xs[n+1..][1..], lt) >= scount(xs[i..][0], xs[i..][1..], lt)
        {
          if i == 0 {
            assert scount(xs[n+1..][0], xs[n+1..][1..], lt) >= scount(xs[i..][0], xs[i..][1..], lt);
          }else{
            assert scount(xs[i..][0], xs[i..][1..], lt) == scount(xs[1..][i-1..][0], xs[1..][i-1..][1..], lt);
            assert scount(xs[n+1..][0], xs[n+1..][1..], lt) >= scount(xs[i..][0], xs[i..][1..], lt);
          }
        }
        LemmaMaxScountEquivalence(xs, n+1, m');
        // assert m == n+1;
        assert msc(xs) == maxScount(xs);
      }
      // LemmaMaximumConcat([xs[0]],xs[1..]);
      // LemmaMaximumOne([xs[0]]);
      assert msc(xs) == maxScount(xs);
    }
  }

  lemma ThereIsAMaxScount(xs: seq<int>)
    requires |xs| > 0
    ensures exists m :: 0 <= m < |xs| && forall i :: 0 <= i < |xs| ==> scount(xs[m..][0], xs[m..][1..], lt) >= scount(xs[i..][0], xs[i..][1..], lt)
  {
    if |xs| == 1 {
      assert xs[1..] == [];
      assert scount(xs[0..][0], xs[0..][1..], lt) == scount(xs[0], xs[1..], lt);
      assert exists m :: 0 <= m < |xs| && forall i :: 0 <= i < |xs| ==> scount(xs[m..][0], xs[m..][1..], lt) >= scount(xs[i..][0], xs[i..][1..], lt);
    }else{
      ThereIsAMaxScount(xs[1..]);
      var m :| 0 <= m < |xs[1..]| && forall i :: 0 <= i < |xs[1..]| ==> scount(xs[1..][m..][0], xs[1..][m..][1..], lt) >= scount(xs[1..][i..][0], xs[1..][i..][1..], lt);
      assert xs == [xs[0]]+xs[1..];
      assert xs[1..][m..] == xs[m+1..];
      assert scount(xs[0..][0], xs[0..][1..], lt) == scount(xs[0], xs[1..], lt);
      assert forall i :: 0 <= i < |xs[1..]| ==> xs[1..][i..] == xs[i+1..];
      if scount(xs[0], xs[1..], lt) > scount(xs[1..][m..][0], xs[1..][m..][1..], lt) {

        forall i | 0 <= i < |xs|
          ensures scount(xs[0], xs[1..], lt) >= scount(xs[i..][0], xs[i..][1..], lt);
        {
          if i == 0 {
          }else{
            assert xs[i..] == xs[1..][(i-1)..];
          }

        }
      }else{
        forall i | 0 <= i < |xs|
          ensures scount(xs[m+1..][0], xs[m+1..][1..], lt) >= scount(xs[i..][0], xs[i..][1..], lt);
        {
          if i == 0 {
            assert scount(xs[m+1..][0], xs[m+1..][1..], lt) >= scount(xs[0], xs[1..], lt);
          }else{
            assert xs[i..] == xs[1..][(i-1)..];
            assert scount(xs[i..][0], xs[i..][1..], lt) == scount(xs[1..][(i-1)..][0], xs[1..][i-1..][1..], lt);
            assert scount(xs[m+1..][0], xs[m+1..][1..], lt) >= scount(xs[i..][0], xs[i..][1..], lt);
          }
        }
      }
      assert exists m :: 0 <= m < |xs| && forall i :: 0 <= i < |xs| ==> scount(xs[m..][0], xs[m..][1..], lt) >= scount(xs[i..][0], xs[i..][1..], lt);

    }
  }

  // lemma mscHasAllGreaterSlices(xs: seq<int>, cpm: (int,int) -> bool, i: nat)
  //     requires 0 <= i < |xs|
  //     requires |xs[i..]| > 0
  //     requires forall z :: z in Filter(y => cpm(xs[i..][0], z), xs[i..]) ==> cpm(xs[i..][0], z)
  // {}

  function table(xs: seq<int>): seq<(int, nat)>
    requires |xs| > 1
  {
    Map((zs) => assume |zs| > 0;
          (zs[0], scount(zs[0], zs[1..], (a,b)=> a < b)), Filter(xxs => |xxs| > 0, Tails(xs)))
  }

  function tcount(z: int, tys: seq<(int, nat)>): nat {
    scount(z, Map((x: (int, nat)) => x.0, tys), (a,b) => a < b)
  }

  function join(txs: seq<(int, nat)>, tys: seq<(int, nat)>): seq<(int, nat)> {
    Map((zc: (int,nat)) =>(zc.0, zc.1+tcount(zc.0, tys)), txs)+tys
  }
}