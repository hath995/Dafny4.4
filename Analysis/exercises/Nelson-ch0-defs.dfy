include "../definitions.dfy"

module NelsonCh0Defs {
    import opened Analysis

    predicate boundedOutput(f: real --> real, x: real, M: real)
        requires f.requires(x)
    {
        abs(f(x)) <= M
    }

    ghost predicate isBoundedBetween(f: real --> real, a: real, b: real, M: real)
        requires M > 0.0
    {
        forall x: real :: a <= x <= b ==> if f.requires(x) then boundedOutput(f, x, M) else false
    }

    ghost predicate isBounded(f: real --> real, a: real, b: real) {
        exists M: real :: M > 0.0 && isBoundedBetween(f, a, b, M)
    }

    lemma functionBoundedInMiddle(f: real --> real, a: real, b: real, c: real)
        requires a < c < b
        requires isBounded(f, a, b)
        ensures isBounded(f, a, c)
        ensures isBounded(f, c, b)
    {
        var M :| M > 0.0 && isBoundedBetween(f, a, b, M);
        assert isBoundedBetween(f, a, c, M);
        assert isBoundedBetween(f, c, b, M);
    }

    ghost function BoundedFunctions(a: real, b: real): iset<real -> real> 
        requires a <= b
    {
        iset f: real -> real | isBounded(f, a, b)
    }

    lemma BoundedFunctionsSubset(a: real, b: real, c: real, f: real -> real)
        requires a < c < b
        requires isBounded(f, a, b)
        ensures isBounded(f, c, b)
    {
        var M :| M > 0.0 && isBoundedBetween(f, a, b, M);
        assert isBoundedBetween(f, c, b, M);
    }

    lemma BoundedFunctionsSubsetLower(a: real, b: real, c: real, f: real -> real)
        requires a < c < b
        requires isBounded(f, a, b)
        ensures isBounded(f, a, c)
    {
        var M :| M > 0.0 && isBoundedBetween(f, a, b, M);
        assert isBoundedBetween(f, a, c, M);
    }

    ghost function funcRange(f: real --> real, a: real, b: real): iset<real>
        requires forall x :: a <= x <= b ==> f.requires(x)
    {
        iset x | a <= x <= b :: f(x)
    }

    ghost function infimum(ms: iset<real>, val: real, lbound: real): real
        requires val in ms
        requires lowerBound(ms, lbound)
        ensures inf(ms, infimum(ms, val, lbound))
    {
        CompletenessAxiomLower(ms, lbound);
        var inf_ms :| inf(ms, inf_ms);
        inf_ms
    }

    lemma infimumUnique(ms: iset<real>, val: real, val': real, bound: real, bound': real)
        requires val in ms
        requires val' in ms
        requires lowerBound(ms, bound)
        requires lowerBound(ms, bound')
        ensures infimum(ms, val, bound) == infimum(ms, val', bound')
    {
    }
    
    lemma infimumInfSame(ms: iset<real>, val: real, bound: real, m: real)
        requires val in ms
        requires lowerBound(ms, bound)
        requires inf(ms, m)
        ensures infimum(ms, val, bound) == m
    {
        infAllUnique(ms, m);
    }

    ghost function supremum(ms: iset<real>, val: real, ubound: real): real
        requires val in ms
        requires upperBound(ms, ubound)
        ensures sup(ms, supremum(ms, val, ubound))
    {
        CompletenessAxiomUpper(ms, ubound);
        var sup_ms :| sup(ms, sup_ms);
        sup_ms
    }


    lemma BoundedBelow(f: real --> real, a: real, b: real, c: real, d: real, M: real) 
        requires M > 0.0
        requires a < b
        requires a <= c < d <= b
        requires forall x :: a <= x <= b ==> f.requires(x)
        requires isBoundedBetween(f, a, b, M)
        ensures lowerBound(funcRange(f, c, d), -M)
    {}

    lemma BoundedAbove(f: real --> real, a: real, b: real, c: real, d: real, M: real) 
        requires M > 0.0
        requires a < b
        requires a <= c < d <= b
        requires forall x :: a <= x <= b ==> f.requires(x)
        requires isBoundedBetween(f, a, b, M)
        ensures upperBound(funcRange(f, c, d), M)
    {}


    predicate Ordered(xs: seq<real>) {
        forall i,j :: 0 <= i < j < |xs| ==> xs[i] < xs[j]
    }

    datatype Partition = Partition(xs: seq<real>, s: set<real>)

    predicate PartitionOf(a: real, b: real, p: Partition)
        requires a < b
    {
        a in p.s
        && b in p.s
        && |p.xs| > 1
        && (forall x :: x in p.s ==> x in p.xs)
        && (forall x :: x in p.xs ==> x in p.s)
        && (forall x :: x in p.xs ==> a <= x <= b)
        && Ordered(p.xs)
        && p.xs[0] == a
        && p.xs[|p.xs|-1] == b
    }

    predicate PartitionPartial(a: real, b: real, p: Partition)
        requires a < b
    {
        b in p.s
        && |p.xs| > 1
        && (forall x :: x in p.s ==> x in p.xs)
        && (forall x :: x in p.xs ==> x in p.s)
        && Ordered(p.xs)
        && (forall x :: x in p.xs ==> a <= x <= b)
        && p.xs[|p.xs|-1] == b
    }

    lemma PartitionPointsBetweenAB(p: Partition, a: real, b: real)
        requires a < b
        requires PartitionOf(a,b, p)
        ensures forall x :: x in p.s ==> a <= x <= b
    {
    }

    lemma infUnique(ms: iset<real>, m: real, m': real)
        requires inf(ms, m)
        requires inf(ms, m')
        ensures m == m'
    {
        if m != m' {
            assert lowerBound(ms, m);
            assert lowerBound(ms, m');
            if m < m' {
                var diff := m' - m;
                // assert diff > 0.0;
                assert m' == add(m, diff);
                // assert m < m+diff < m';
                // assert lowerBound(ms, m+diff);
                // assert !greatestLeastBound(ms, m');
            } else {
                var diff := m - m';
                assert m' == add(m', diff);
            }

            assert false;
            // assert m' <= m;
        }
    }

    lemma infAllUnique(ms: iset<real>, m: real)
        requires inf(ms, m)
        ensures forall m' :: inf(ms, m') ==> m' == m
    {
        forall m' | inf(ms, m') 
            ensures m' == m
        {
            infUnique(ms, m, m');
        }
    }

    lemma supUnique(ms: iset<real>, m: real, m': real)
        requires sup(ms, m)
        requires sup(ms, m')
        ensures m == m'
    {
        if m != m' {
            assert upperBound(ms, m);
            assert upperBound(ms, m');
            if m < m' {
                var diff := m' - m;
                assert m == sub(m', diff);
            } else {
                assert m > m';
                var diff := m - m';
                assert m' == sub(m, diff);
            }
            assert false;
        }
    }

    lemma supAllUnique(ms: iset<real>, m: real)
        requires sup(ms, m)
        ensures forall m' :: sup(ms, m') ==> m' == m
    {
        forall m' | sup(ms, m') 
            ensures m' == m
        {
            supUnique(ms, m, m');
        }
    }

}