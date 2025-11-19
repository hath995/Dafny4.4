include "./SeqFunctions.dfy"
module SurpassingProblem {
    import opened SeqFunctions
    function Tails<T>(xs: seq<T>): seq<seq<T>> {
        if xs == [] then
            []
        else
            [xs]+Tails(xs[1..])
    }

    function scount<T>(x: T, xs: seq<T>, cpm: (T,T) -> bool): nat {
        |Filter(y => cpm(x,y) ,xs)|
    }

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

    function msc(xs: seq<int>): nat 
        requires |xs| > 1
    {
        var zzs := Map((zs) => assume |zs| > 0;
            scount(zs[0], zs[1..], (a,b)=> a < b), Filter(xxs => |xxs| > 0, Tails(xs)));
        maximum(zzs)
    }

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