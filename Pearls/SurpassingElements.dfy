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
  lemma LemmaMaximumConcat(xs: seq<nat>, ys: seq<nat>)
    requires |ys| > 0
    requires |xs| > 0
    ensures maximum(xs+ys) == maxNat(maximum(xs), maximum(ys))
  {
    if |xs| == 1 {

    }else{
      LemmaMaximumConcat(xs[1..], ys);
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
        maxNat(xs[0], FoldRight(maxNat, xs[1..], xs[0]));
        maxNat(xs[0], FoldRight(maxNat, [], xs[0]));
        maxNat(xs[0], xs[0]);
        xs[0];
      }
      assert maximum(xs) in xs;
    }else{
      assert xs == [xs[0]]+xs[1..];
      LemmaMaximumIn(xs[1..]);
      LemmaFoldRightDistributesOverConcat(maxNat,xs[0], [xs[0]],xs[1..]);

      calc {
        maximum(xs);
        FoldRight(maxNat, xs, xs[0]);
        FoldRight(maxNat, [xs[0]], FoldRight(maxNat, xs[1..], xs[0]));
        // maxNat(xs[0], FoldRight(maxNat, xs[1..], xs[0]));
      }
      if xs[0] >  maximum(xs[1..]) {

        assert maximum(xs) in xs;
      }else{

        assert maximum(xs) in xs;
      }
      assert maximum(xs) in xs;

    }
  }

  ghost function maxScount(xs: seq<int>): nat
    requires |xs| > 0
  {
    ThereIsAMaxScount(xs);
    var m :| 0 <= m < |xs| && forall i :: 0 <= i < |xs| ==> scount(xs[m..][0], xs[m..][1..], (a,b) => a <b) >= scount(xs[i..][0], xs[i..][1..], (a,b) => a <b);
    scount(xs[m..][0], xs[m..][1..], (a,b) => a < b)
  }

  function msc(xs: seq<int>): nat
    requires |xs| > 0
  {
    var zzs := Map((zs) => assume |zs| > 0;
                     scount(zs[0], zs[1..], (a,b)=> a < b), Tails(xs));
    maximum(zzs)
  }

  lemma {:isolate_assertions} mscIsMaximum(xs: seq<int>)
    requires |xs| > 0
    ensures msc(xs) == maxScount(xs)
  {
    if |xs| == 1 {
      assert xs[1..] == [];
      assert Tails(xs) == [xs] + Tails(xs[1..]);
      assert Tails(xs) == [xs];
      assert Filter(xxs => |xxs| > 0, Tails(xs)) == [xs];
      assert scount(xs[0..][0], xs[0..][1..], (a,b) => a <b) == scount(xs[0], xs[1..], (a,b) => a <b);
      ThereIsAMaxScount(xs);
      var m :| 0 <= m < |xs| && forall i :: 0 <= i < |xs| ==> scount(xs[m..][0], xs[m..][1..], (a,b) => a <b) >= scount(xs[i..][0], xs[i..][1..], (a,b) => a <b);
      assert m == 0;
      assert msc(xs) == maxScount(xs);
    }else{
      mscIsMaximum(xs[1..]);
      assert xs == [xs[0]]+xs[1..];
      assert msc(xs) == maxScount(xs);
    }
  }

  lemma ThereIsAMaxScount(xs: seq<int>)
    requires |xs| > 0
    ensures exists m :: 0 <= m < |xs| && forall i :: 0 <= i < |xs| ==> scount(xs[m..][0], xs[m..][1..], (a,b) => a <b) >= scount(xs[i..][0], xs[i..][1..], (a,b) => a <b)
  {
    if |xs| == 1 {
      assert xs[1..] == [];
      assert scount(xs[0..][0], xs[0..][1..], (a,b) => a <b) == scount(xs[0], xs[1..], (a,b) => a <b);
      assert exists m :: 0 <= m < |xs| && forall i :: 0 <= i < |xs| ==> scount(xs[m..][0], xs[m..][1..], (a,b) => a <b) >= scount(xs[i..][0], xs[i..][1..], (a,b) => a <b);
    }else{
      ThereIsAMaxScount(xs[1..]);
      var m :| 0 <= m < |xs[1..]| && forall i :: 0 <= i < |xs[1..]| ==> scount(xs[1..][m..][0], xs[1..][m..][1..], (a,b) => a <b) >= scount(xs[1..][i..][0], xs[1..][i..][1..], (a,b) => a <b);
      assert xs == [xs[0]]+xs[1..];
      assert xs[1..][m..] == xs[m+1..];
      assert scount(xs[0..][0], xs[0..][1..], (a,b) => a <b) == scount(xs[0], xs[1..], (a,b) => a <b);
      assert forall i :: 0 <= i < |xs[1..]| ==> xs[1..][i..] == xs[i+1..];
      if scount(xs[0], xs[1..], (a,b) => a <b) > scount(xs[1..][m..][0], xs[1..][m..][1..], (a,b) => a <b) {

        forall i | 0 <= i < |xs|
          ensures scount(xs[0], xs[1..], (a,b) => a <b) >= scount(xs[i..][0], xs[i..][1..], (a,b) => a <b);
        {
          if i == 0 {
          }else{
            assert xs[i..] == xs[1..][(i-1)..];
          }

        }
      }else{
        forall i | 0 <= i < |xs|
          ensures scount(xs[m+1..][0], xs[m+1..][1..], (a,b) => a <b) >= scount(xs[i..][0], xs[i..][1..], (a,b) => a <b);
        {
          if i == 0 {
            assert scount(xs[m+1..][0], xs[m+1..][1..], (a,b) => a <b) >= scount(xs[0], xs[1..], (a,b) => a <b);
          }else{
            assert xs[i..] == xs[1..][(i-1)..];
            assert scount(xs[i..][0], xs[i..][1..], (a,b) => a <b) == scount(xs[1..][(i-1)..][0], xs[1..][i-1..][1..], (a,b) => a <b);
            assert scount(xs[m+1..][0], xs[m+1..][1..], (a,b) => a <b) >= scount(xs[i..][0], xs[i..][1..], (a,b) => a <b);
          }
        }
      }
      assert exists m :: 0 <= m < |xs| && forall i :: 0 <= i < |xs| ==> scount(xs[m..][0], xs[m..][1..], (a,b) => a <b) >= scount(xs[i..][0], xs[i..][1..], (a,b) => a <b);

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