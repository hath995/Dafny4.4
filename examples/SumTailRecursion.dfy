

module TailRecPrep {

    function Sum(xs: seq<int>): int {
        if xs == [] then 0 else xs[0] + Sum(xs[1..])
    } by method {
        var sum := 0;
        var i := 0;
        while i < |xs|
            invariant 0 <= i <= |xs|
            invariant sum == Sum(xs[0..i])
        {
            sum := sum + xs[i];
            assert xs[0..i+1] == xs[0..i] + [xs[i]];
            SumConcat(xs[0..i], [xs[i]]);
            i := i + 1;
        }
        assert i == |xs|;
        assert xs == xs[0..i];
        return sum;
    }

    function SumReverse(xs: seq<int>): int {
        if xs == [] then 0 else xs[|xs| - 1] + SumReverse(xs[0..|xs| - 1])
    }

    lemma SumConcat(xs: seq<int>, ys: seq<int>)
        ensures Sum(xs + ys) == Sum(xs) + Sum(ys)
    {
        if xs == [] {
            assert xs + ys == ys;
        }else if ys == [] {
            assert xs + ys == xs;
            assert Sum(xs + ys) == Sum(xs);
        }else{
            SumConcat(xs[1..], ys);
            assert (xs + ys)[1..] == xs[1..] + ys;
            // assert xs + ys == [xs[0]] + xs[1..] + ys;
            // calc {
            //     Sum(xs + ys);
            //     Sum([xs[0]] + xs[1..] + ys);
            //     xs[0] + Sum(xs[1..] + ys);
            //     xs[0] + Sum(xs[1..]) + Sum(ys);
            //     xs[0] + Sum(xs[1..]+ys);
            // }
        }
    }

    lemma SumReverseConcat(xs: seq<int>, ys: seq<int>)
        ensures SumReverse(xs + ys) == SumReverse(ys) + SumReverse(xs)
    {
        if xs == [] {
            assert xs + ys == ys;
        }else if ys == [] {
            assert xs + ys == xs;
            assert SumReverse(xs + ys) == SumReverse(xs);
        }else{
            SumReverseConcat(xs, ys[..|ys| - 1]);
            assert (xs + ys)[0..(|xs| + |ys| - 1)] == xs + ys[0..|ys| - 1];
        }
    }

    lemma  SumAssociative(xs: seq<int>, ys: seq<int>, zs: seq<int>)
        ensures Sum(xs + ys) + Sum(zs) == Sum(xs) + Sum(ys + zs)
    {
        if xs == [] {
            assert xs + ys == ys;
            assert Sum(xs + ys) == Sum(ys);
            SumConcat(ys, zs);
            assert Sum(xs + ys) + Sum(zs) == Sum(xs) + Sum(ys + zs);
        }else if ys == [] {
            assert xs + ys == xs;
            assert Sum(xs + ys) == Sum(xs);
            SumConcat(xs, zs);
            assert Sum(xs + ys) + Sum(zs) == Sum(xs) + Sum(ys + zs);
        }else if zs == [] {
            SumConcat(xs, ys);
            assert Sum(xs + ys) + Sum(zs) == Sum(xs) + Sum(ys + zs);
        }else{
            // SumAssociative(xs[1..], ys, zs);
            // assert (xs + ys)[1..] == xs[1..] + ys;
            assert Sum(xs + ys) + Sum(zs) == Sum(xs) + Sum(ys + zs);
        }
    }

    lemma SumReverseEqualsSum(xs: seq<int>)
        ensures SumReverse(xs) == Sum(xs)
    {
        if xs == [] {
            assert xs == [];
        }else if |xs| == 1 {
            assert xs == [xs[0]];
            assert SumReverse(xs) == xs[0];
            assert Sum(xs) == xs[0];
        }else{
            // SumReverseEqual(xs[0..|xs| - 1]);
            assert xs == [xs[0]] + xs[1..];
            assert xs == xs[..|xs| - 1] + [xs[|xs| - 1]];
            SumConcat([xs[0]], xs[1..]);
            SumConcat(xs[..|xs| - 1], [xs[|xs| - 1]]);
            SumReverseConcat(xs[1..], [xs[|xs| - 1]]);
            SumReverseConcat([xs[0]], xs[1..]);
            SumReverseEqualsSum(xs[1..]);
            SumReverseEqualsSum([xs[0]]);
            SumReverseEqualsSum(xs[..|xs| - 1]);
            SumReverseEqualsSum([xs[|xs| - 1]]);
            assert SumReverse(xs) == Sum(xs);
        }
    }

    function SumTailRecHelper(xs: seq<int>, acc: int, ghost i: int, ghost xxs: seq<int>): int
        requires 0 <= i <= |xxs|
        requires acc == Sum(xxs[0..i])
        requires xs == xxs[i..]
        ensures xs == [] ==> SumTailRecHelper(xs, acc, i, xxs) == acc
        // ensures xs != [] ==> SumTailRecHelper(xs[1..], acc + xs[0], i + 1, xxs) == SumTailRecHelper([], acc+Sum(xxs[i..]), |xxs|, xxs)
    {
        if xs == [] then
            acc
        else 
            SumConcat(xxs[0..i], [xs[0]]);
            assert xs == [xs[0]] + xs[1..];
            assert xxs == xxs[0..i] + [xs[0]] + xs[1..];
            SumTailRecHelper(xs[1..], acc + xs[0], i + 1, xxs)
    }

    lemma SumTailRecHelperResult(xs: seq<int>, acc: int, i: int, xxs: seq<int>)
        requires i == |xxs|
        requires acc == Sum(xxs[0..i])
        requires xs == xxs[i..]
        ensures SumTailRecHelper(xs, acc, i, xxs) ==  Sum(xxs)
    {
        assert xxs == xxs[..i];
        assert xs == [];
        assert acc == Sum(xxs);
    }

    lemma SumTailRecCompletes(xs: seq<int>, acc: int, i: int, xxs: seq<int>)
        requires 0 <= i <= |xxs|
        requires acc == Sum(xxs[0..i])
        requires xs == xxs[i..]
        ensures SumTailRecHelper(xs, Sum(xxs[0..i]), i, xxs) == SumTailRecHelper([], Sum(xxs[0..|xxs|]), |xxs|, xxs)
    {
       if xs == [] {
            assert xxs == xxs[..i];
            assert acc == Sum(xxs);
            assert i == |xxs|;
            SumTailRecHelperResult(xs, acc, i, xxs);
            assert SumTailRecHelper(xs, Sum(xxs[0..i]), i, xxs) == SumTailRecHelper([], Sum(xxs[0..|xxs|]), |xxs|, xxs);
        }else{
            assert xxs == xxs[0..i] + [xs[0]] + xs[1..];
            SumConcat(xxs[0..i], [xs[0]]);
            SumTailRecCompletes(xs[1..], acc + xs[0], i + 1, xxs);
        } 
    }

    function SumTailRec(xs: seq<int>): int
        ensures SumTailRec(xs) == Sum(xs)
    {
        assert xs == xs[0..|xs|];
        SumTailRecCompletes(xs, 0, 0, xs);
        assert SumTailRecHelper(xs, 0, 0, xs) == SumTailRecHelper([], Sum(xs[0..|xs|]), |xs|, xs);
        SumTailRecHelperResult([], Sum(xs), |xs|, xs);
        SumTailRecHelper(xs, 0, 0, xs)
    }

    function Fibonacci(i: nat): nat {
        if i <= 1 then i else Fibonacci(i-1)+Fibonacci(i-2)
    }  by method {
        if i <= 1 {
            return i;
        }
        var n := 2;
        var a, b := 0, 1;

        while n <= i
            invariant 1 < n <= i+1
            invariant a == Fibonacci(n-2)
            invariant b == Fibonacci(n-1)
        {
            a,b := b, a+b;
            n := n + 1;
        }
        return b;
    }

    function FibTail(n: nat, a: nat, b:nat, i: nat): nat
        requires 1 < n <= i
        requires a == Fibonacci(n-2)
        requires b == Fibonacci(n-1)
        ensures FibTail(n, a, b, i) == Fibonacci(i)
        decreases i-n
    {
        if n == i then a+b else
        FibTail(n+1,b,a+b,i)
    }

    function Fib(i: nat): nat 
        ensures Fib(i) == Fibonacci(i)
    {
        if i <= 1 then i else
        // FibTailResult(2, i);
        // FibTailResultEnd(i);
        FibTail(2, 0, 1, i)
    }

    lemma FibTailResult(n: nat, i: nat)
        requires i > 1
        requires 1 < n <= i
        ensures FibTail(n, Fibonacci(n-2), Fibonacci(n-1), i) == FibTail(i, Fibonacci(i-2), Fibonacci(i-1), i)
        decreases i-n
    {
        if n == i {
        } else {
            FibTailResult(n+1, i);
        }
    }

    lemma FibTailResultEnd(i: nat)
        requires 1 < i
        ensures FibTail(i, Fibonacci(i-2), Fibonacci(i-1), i) == Fibonacci(i)
    {}
}