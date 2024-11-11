include "../definitions.dfy"

module NelsonCh0 {
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

    function oneOverX(x: real): real 
        requires x != 0.0
    {
        1.0 / x
    }

    lemma oneOverXNotInB_zero_one()
        ensures oneOverX !in BoundedFunctions(0.0,1.0)
    {
        assert oneOverX !in BoundedFunctions(0.0, 1.0) by {
            forall M: real | M > 0.0
                ensures !isBoundedBetween(oneOverX, 0.0, 1.0, M)
            {
                assert !oneOverX.requires(0.0);
                // assume exists x :: 0.0 <= x <= 1.0 && x != 0.0 && abs(oneOverX(x)) > M;
                // var x :| 0.0 <= x <= 1.0 && x != 0.0 && abs(oneOverX(x)) > M;
                // assert !boundedOutput(oneOverX, x, M);
            }
        }
    }

    lemma oneOverXInB_one_two()
        // ensures oneOverX in BoundedFunctions(1.0,2.0)
        ensures isBounded(oneOverX, 1.0, 2.0)
    {
        var M := 1.0;
        assert M > 0.0;
        assert forall x :: 1.0 <= x <= 2.0 ==> oneOverX.requires(x);
        assert forall x :: 1.0 <= x <= 2.0 ==> boundedOutput(oneOverX, x, M);
        assert isBoundedBetween(oneOverX, 1.0, 2.0, M);
        assert isBounded(oneOverX, 1.0, 2.0);
        //function exstensionality is not supported in Dafny
        // assert oneOverX in BoundedFunctions(1.0, 2.0) by {}
    }

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
        && p.xs[|p.xs|-1] == b
    }

    predicate PartitionPartial(a: real, b: real, p: Partition)
        requires a < b
    {
        b in p.s
        && |p.xs| >= 1
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

    ghost function LowerSum(f: real -> real, P: Partition, a: real, b: real): real 
        requires a < b
        requires isBounded(f, a, b)
        requires PartitionOf(a,b, P)
    {
        PartitionPointsBetweenAB(P, a, b);
        LowerSumHelper(f, P, a, b, 1)
    }

    ghost function LowerSumHelper(f: real -> real, P: Partition, a: real, b: real, i: nat): real 
        requires a < b
        requires isBounded(f, a, b)
        requires PartitionPartial(a,b, P)
        requires 1 <= i < |P.xs|
        decreases |P.xs|-i
    {
        // var ms := iset x | P.xs[i-1] <= x <= P.xs[i] :: f(x);
        var ms := funcRange(f, P.xs[i-1], P.xs[i]);
        var q := f(P.xs[i-1]);
        assert q in ms;
        var M :| M > 0.0 && isBoundedBetween(f,a,b,M);
        assert P.xs[i-1] in P.xs;
        BoundedBelow(f, a, b, P.xs[i-1], P.xs[i], M);
        var m_i := infimum(ms, q, -M);
        if i == |P.xs|-1 then m_i * (P.xs[i] - P.xs[i-1]) else m_i * (P.xs[i] - P.xs[i-1]) + LowerSumHelper(f, P, a, b, i+1)
    }

    ghost function LowerSumAlt(f: real -> real, P: Partition, a: real, b: real): real 
        requires a < b
        requires isBounded(f, a, b)
        requires |P.xs| > 1
        requires PartitionPartial(a,b, P)
        decreases |P.xs|
    {
        var ms := funcRange(f, P.xs[0], P.xs[1]);
        var q := f(P.xs[0]);
        assert q in ms;
        var M :| M > 0.0 && isBoundedBetween(f,a,b,M);
        assert P.xs[0] in P.xs;
        BoundedBelow(f, a, b, P.xs[0], P.xs[1], M);
        var m_0 := infimum(ms, q, -M);
        var res := m_0*(P.xs[1]-P.xs[0]);
        if |P.xs| == 2 then res else res + LowerSumAlt(f, Partition(P.xs[1..], P.s - {P.xs[0]}), a, b)
    }

    function PartitionRemoveIndex(p: Partition, a: real, b: real, i: nat): Partition
        requires a < b
        requires |p.xs| > 2
        requires 0 < i < |p.xs|-1
        requires PartitionOf(a,b, p)
        ensures PartitionOf(p.xs[0], p.xs[|p.xs|-1], Partition(xs := p.xs[..i] + p.xs[i+1..], s := p.s - {p.xs[i]}))
    {
        Partition(p.xs[..i] + p.xs[i+1..], p.s - {p.xs[i]})
    }

    lemma LowerSumConcat(f: real -> real, P: Partition, P_1: Partition, P_2: Partition, a: real, b: real, c: real)
        requires a < c < b
        requires isBounded(f, a, b)
        requires isBounded(f, a, c)
        requires isBounded(f, c, b)
        requires PartitionOf(a,c, P_1)
        requires PartitionOf(c,b, P_2)
        requires P == Partition(P_1.xs[..|P_1.xs|-1]+P_2.xs, P_1.s+P_2.s)
        requires PartitionOf(a,b, P)
        ensures LowerSum(f, P, a, b) == LowerSum(f, P_1, a, c) + LowerSum(f, P_2, c, b)
    {
        if |P_1.xs| == 2 {
            var ms := funcRange(f, P_1.xs[0], P_1.xs[1]);
            var q := f(P_1.xs[0]);
            assert q in ms;
            var M :| M > 0.0 && isBoundedBetween(f,a,b,M);
            BoundedBelow(f, a, b, P_1.xs[0], P_1.xs[1], M);
            var m_0 := infimum(ms, q, -M);
            infAllUnique(ms, m_0);
            calc {
                LowerSum(f, P_1, a, c);
                LowerSumHelper(f, P_1, a, c, 1);
                m_0*(P_1.xs[1]-P.xs[0]);
            }
            assert P.xs[0] == P_1.xs[0];
            assert P.xs[1] == P_1.xs[1];
            calc {
                LowerSum(f, P, a, b);
                LowerSumHelper(f, P, a, b, 1);
                m_0*(P_1.xs[1]-P.xs[0]) + LowerSumHelper(f, P, a,b, 2);
            }
            assert LowerSum(f, P_2, c, b) == LowerSumHelper(f, P, a, b, 2);
            assert LowerSum(f, P, a, b) == LowerSum(f, P_1, a, c) + LowerSum(f, P_2, c, b);
        }else{

            assert LowerSum(f, P, a, b) == LowerSum(f, P_1, a, c) + LowerSum(f, P_2, c, b);
        }
    }

    lemma {:verify false} LowerSumPartial(f: real -> real, P: Partition, a: real, b: real, i: nat, m_i: real)
        requires a < b
        requires f in BoundedFunctions(a, b)
        requires PartitionOf(a,b, P)
        requires 1 <= i < |P.xs|-1
        requires inf(funcRange(f, P.xs[i-1], P.xs[i]), m_i)
        ensures LowerSum(f, P, a, b) == m_i * (P.xs[i] - P.xs[i-1]) + LowerSum(f, PartitionRemoveIndex(P, a, b, i), a, b)
    {
        if |P.xs| == 2 {
            assert LowerSum(f, P, a, b) == m_i * (P.xs[i] - P.xs[i-1]);
        } else {
            var l := LowerSum(f, P, a, b);
            var l' := m_i * (P.xs[i] - P.xs[i-1]) + LowerSum(f, PartitionRemoveIndex(P, a, b, i), a, b);
            assert l == l';
        }
        //var l := LowerSum(f, P, a, b);
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

    ghost function UpperSum(f: real -> real, P: Partition, a: real, b: real): real 
        requires a < b
        requires f in BoundedFunctions(a, b)
        requires PartitionOf(a,b, P)
    {
        UpperSumHelper(f, P, a, b, 1)
    }

    ghost function UpperSumHelper(f: real -> real, P: Partition, a: real, b: real, i: nat): real 
        requires a < b
        requires f in BoundedFunctions(a, b)
        requires PartitionPartial(a,b, P)
        requires 1 <= i < |P.xs|
        decreases |P.xs|-i
    {
        var ms := iset x | P.xs[i-1] <= x <= P.xs[i] :: f(x);
        var q := f(P.xs[i-1]);
        assert q in ms;
        var M :| M > 0.0 && isBoundedBetween(f,a,b,M);
        assert P.xs[i-1] in P.xs;
        BoundedAbove(f, a, b, P.xs[i-1], P.xs[i], M);
        CompletenessAxiomUpper(ms, M);
        var M_i :| sup(ms, M_i);
        if i == |P.xs|-1 then M_i * (P.xs[i] - P.xs[i-1]) else M_i * (P.xs[i] - P.xs[i-1]) + UpperSumHelper(f, P, a, b, i+1)
    }

    lemma AllPartitionSetBoundedLow(f: real -> real, a: real, b: real, M: real, fsup: real, P: Partition)
        requires a < b
        requires M > 0.0
        requires isBoundedBetween(f, a, b, M)
        requires PartitionOf(a,b, P)
        requires sup(funcRange(f, a, b), fsup)
        ensures LowerSum(f, P, a, b) <= (b-a) * M
    {}

    lemma AllPartitionSetBoundedUpper(f: real -> real, a: real, b: real, M: real, P: Partition)
        requires a < b
        requires M > 0.0
        requires isBoundedBetween(f, a, b, M)
        requires PartitionOf(a,b, P)
        ensures UpperSum(f, P, a, b) >= (b-a) * -M
    {}


    ghost function LowerIntegral(f: real -> real, a: real, b: real): real 
        requires a < b
        requires isBounded(f, a, b)
    {
        var M :| M > 0.0 && isBoundedBetween(f,a,b,M);
        var allPartitions := iset P | PartitionOf(a,b, P);
        var allPartitionSums := iset P | P in allPartitions :: LowerSum(f, P, a, b);
        var canonical_P := Partition([a, b], {a, b});
        var x := LowerSum(f, canonical_P, a, b);
        assert x in allPartitionSums;
        CompletenessAxiomUpper(allPartitionSums, x);
        var fsup :| sup(allPartitionSums, fsup);
        
        assert forall sum :: sum in allPartitionSums ==> sum <= (b-a)*M by {
            forall sum | sum in allPartitionSums
                ensures sum <= (b-a)*M
            {
                var P :| P in allPartitions && sum == LowerSum(f, P, a, b);
                AllPartitionSetBoundedLow(f, a, b, M, fsup, P);
            }
        }
       supremum(allPartitionSums, x,  (b-a)*M)
    }

    ghost function UpperIntegral(f: real -> real, a: real, b: real): real 
        requires a < b
        requires isBounded(f, a, b)
    {
        var M :| M > 0.0 && isBoundedBetween(f,a,b,M);
        var allPartitions := iset P | PartitionOf(a,b, P);
        var allPartitionSums := iset P | P in allPartitions :: UpperSum(f, P, a, b);
        var canonical_P := Partition([a, b], {a, b});
        var x := UpperSum(f, canonical_P, a, b);
        assert forall sum :: sum in allPartitionSums ==> sum >= (b-a)*-M by {
            forall sum | sum in allPartitionSums
                ensures sum >= (b-a)*-M
            {
                var P :| P in allPartitions && sum == UpperSum(f, P, a, b);
                AllPartitionSetBoundedUpper(f, a, b, M, P);
            }
        }
        infimum(allPartitionSums, x, (b-a)*-M)
    }

    ghost predicate RiemannIntegrable(f: real -> real, a: real, b: real) {
        a < b && isBounded(f, a, b) && LowerIntegral(f, a, b) == UpperIntegral(f, a, b)
    }


    lemma Prop_zero_one_six(f: real -> real, P: Partition, a: real, b: real, m: real, M: real)
        requires a < b
        requires f in BoundedFunctions(a, b)
        requires PartitionOf(a,b, P)
        requires inf(funcRange(f, a, b), m)
        requires sup(funcRange(f, a, b), M)
        ensures m*(b-a) <= LowerSum(f, P, a, b) <= UpperSum(f, P, a, b) <= M*(b-a)
    {
        Prop_zero_one_six_inf(f, P, a, b, m);
        Prop_zero_one_six_lower_upper(f, P, a, b);
        Prop_zero_one_six_sup(f, P, a, b, M);
    }

    lemma Prop_zero_one_six_inf(f: real -> real, P: Partition, a: real, b: real, m: real)
        requires a < b
        requires f in BoundedFunctions(a, b)
        requires PartitionOf(a,b, P)
        requires inf(funcRange(f, a, b), m)
        ensures m*(b-a) <= LowerSum(f, P, a, b)
    {
        var l := LowerSum(f, P, a, b);
        if P.xs == [a, b] {
            infAllUnique(funcRange(f, P.xs[0], P.xs[1]), m);
            assert m*(b-a) <= l;
        } else {
            // assert l >= m*(b-a);
            assert m*(b-a) <= l;
            //Forall m_i, m <= m_i
            //forall i, sum(P.xs[i+1] - P.xs[i]) == b-a
            //induction on lowerSumHelper up to |P.xs|-1 and 
            // ms == funcRange(f, P.xs[i-1], P.xs[i]) <= funcRange(f, a, b)
            // inf(ms, m_i) ==> m <= m_i
            // if inf(ms, m_i) < m then contradiction
        }
    }

    lemma Prop_zero_one_six_sup(f: real -> real, P: Partition, a: real, b: real, M: real)
        requires a < b
        requires f in BoundedFunctions(a, b)
        requires PartitionOf(a,b, P)
        requires sup(funcRange(f, a, b), M)
        ensures UpperSum(f, P, a, b) <= M*(b-a)
    {
        var u := UpperSum(f, P, a, b);
        assert u <= M*(b-a);
    }

    lemma Prop_zero_one_six_lower_upper(f: real -> real, P: Partition, a: real, b: real)
        requires a < b
        requires f in BoundedFunctions(a, b)
        requires PartitionOf(a,b, P)
        ensures LowerSum(f, P, a, b) <= UpperSum(f, P, a, b)
    {
        var l := LowerSum(f, P, a, b);
        var u := UpperSum(f, P, a, b);
        assert l <= u;
    }

    lemma {:verify false} Problem3(f: real -> real, g: real -> real, a: real, b: real)
        requires a < b
        requires isBounded(f, a, b)
        requires isBounded(g, a, b)
        requires RiemannIntegrable(f, a, b)
        requires RiemannIntegrable(g, a, b)
        requires forall x :: a <= x <= b ==> f(x) <= g(x)
        ensures LowerIntegral(f, a, b) <= LowerIntegral(g, a, b)
    {}

    lemma {:verify } {:vcs_split_on_every_assert} Problem5a(f: real -> real, g: real -> real, a: real, b: real, c: real)
        requires a < b
        requires a <= c <= b
        requires isBounded(f, a, b)
        requires RiemannIntegrable(f, a, b)
        requires forall x :: a <= x <= b && x != c ==> f(x) == g(x)
        ensures RiemannIntegrable(g, a, b)
    {
        assert isBounded(g, a, b) by {
            var M :| M > 0.0 && isBoundedBetween(f, a, b, M);
            if -M <= g(c) <= M {
                assert abs(g(c)) <= M;
                forall x | a <= x <= b && x != c 
                    ensures abs(g(x)) <= M
                {
                    assert f(x) == g(x);
                    assert f.requires(x);
                    assert abs(f(x)) <= M;
                    assert abs(g(x)) <= M;
                }
                assert isBoundedBetween(g, a, b, M);
            } else {
                var C := abs(g(c));
                assert C > 0.0;
                assert M < C;
                assert g.requires(c);
                assert abs(g(c)) <= C;
                forall x | a <= x <= b && x != c 
                    ensures abs(g(x)) <= C
                {
                    assert f(x) == g(x);
                    assert f.requires(x);
                    assert g.requires(x);
                    assert abs(f(x)) <= M;
                    assert abs(g(x)) <= M <= C;
                }
                assert isBoundedBetween(g, a, b, C);
            }
        }
        assume LowerIntegral(g, a, b) == UpperIntegral(g, a, b);
    }

    lemma EqualFunctionUpper(f: real -> real, g: real -> real, a: real, b: real)
        requires a < b
        requires forall x :: a <= x <= b ==> f(x) == g(x)
        requires isBounded(f, a, b)
        requires isBounded(g, a, b)
        ensures UpperIntegral(f, a, b) == UpperIntegral(g, a, b)
    // {
    //     var l := UpperIntegral(f, a, b);
    //     var u := UpperIntegral(g, a, b);
    //     assert l == u;
    // }

    lemma EqualBoundedFunctionsAlsoBounded(f: real -> real, g: real -> real, a: real, b: real)
        requires isBounded(f, a, b)
        requires forall x :: a <= x <= b ==> f(x) == g(x)
        ensures isBounded(g, a, b)
    {
        var M :| M > 0.0 && isBoundedBetween(f, a, b, M);
        forall x | a <= x <= b
            ensures g.requires(x)
        {
        }
        assert isBoundedBetween(g, a, b, M) by {
            forall x | a <= x <= b
                ensures abs(g(x)) <= M
            {
                assert f(x) == g(x);
                assert f.requires(x);
                assert abs(f(x)) <= M;
                assert abs(g(x)) <= M;
            }
        }
    }

    lemma EqualFunctionLower(f: real -> real, g: real -> real, a: real, b: real)
        requires a < b
        requires forall x :: a <= x <= b ==> f(x) == g(x)
        requires isBounded(f, a, b)
        requires isBounded(g, a, b)
        ensures LowerIntegral(f, a, b) == LowerIntegral(g, a, b)

    lemma {:verify } {:vcs_split_on_every_assert} Problem5b(f: real -> real, g: real -> real, a: real, b: real, diffpoints: set<real>)
        requires a < b
        requires forall c :: c in diffpoints ==> a <= c <= b
        requires isBounded(f, a, b)
        requires RiemannIntegrable(f, a, b)
        requires forall x :: a <= x <= b && x !in diffpoints ==> f(x) == g(x)
        ensures RiemannIntegrable(g, a, b)
    {
        if |diffpoints| == 0 {
            EqualBoundedFunctionsAlsoBounded(f, g, a, b);
            EqualFunctionLower(f, g, a, b);
            EqualFunctionUpper(f, g, a, b);
            assert RiemannIntegrable(g, a, b);
        } else if |diffpoints| == 1 {
            var c :| c in diffpoints;
            assert diffpoints == {c} by {
                assert |diffpoints| == 1;
                assert |diffpoints - {c}| == 0;
                assert diffpoints - {c} == {};
            }
            forall x | a <= x <= b && x != c
                ensures f(x) == g(x)
            {
                assert x != c;
                assert x !in diffpoints;
            }
            Problem5a(f, g, a, b, c);
        } else {
            var c :| c in diffpoints;
            Problem5b(f, g, a, b, diffpoints-{c});
            Problem5a(f, g, a, b, c);
        }
    }
}

