include "../definitions.dfy"
include "./Nelson-ch0-defs.dfy"
module NelsonCh0 {
    import opened Analysis
    import opened NelsonCh0Defs

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


    // ghost function LowerSum(f: real -> real, P: Partition, a: real, b: real): real 
    //     requires a < b
    //     requires isBounded(f, a, b)
    //     requires PartitionOf(a,b, P)
    // {
    //     PartitionPointsBetweenAB(P, a, b);
    //     LowerSumHelper(f, P, a, b, 1)
    // }

    // ghost function LowerSumHelper(f: real -> real, P: Partition, a: real, b: real, i: nat): real 
    //     requires a < b
    //     requires isBounded(f, a, b)
    //     requires PartitionPartial(a,b, P)
    //     requires 1 <= i < |P.xs|
    //     decreases |P.xs|-i
    // {
    //     // var ms := iset x | P.xs[i-1] <= x <= P.xs[i] :: f(x);
    //     var ms := funcRange(f, P.xs[i-1], P.xs[i]);
    //     var q := f(P.xs[i-1]);
    //     assert q in ms;
    //     var M :| M > 0.0 && isBoundedBetween(f,a,b,M);
    //     assert P.xs[i-1] in P.xs;
    //     BoundedBelow(f, a, b, P.xs[i-1], P.xs[i], M);
    //     var m_i := infimum(ms, q, -M);
    //     if i == |P.xs|-1 then m_i * (P.xs[i] - P.xs[i-1]) else m_i * (P.xs[i] - P.xs[i-1]) + LowerSumHelper(f, P, a, b, i+1)
    // }

    ghost function InfWidth(f: real -> real, x: real, y: real, ms: iset<real>): real 
        requires x < y
        requires ms == funcRange(f, x, y)
        requires isBounded(f, x, y)
        ensures exists i_a :: inf(ms, i_a)
        ensures forall i_b :: inf(ms, i_b) ==> InfWidth(f, x, y, ms) == prod(i_b, sub(y,x)) 
    {
        var q := f(x);
        assert q in ms;
        var M :| M > 0.0 && isBoundedBetween(f,x,y,M);
        BoundedBelow(f, x, y, x, y, M);
        infAllUnique(ms, infimum(ms, q, -M));
        prod(infimum(ms, q, -M),sub(y,x))
    }

    lemma InfWidthSame(f: real -> real, x: real, y: real, ms: iset<real>, m: real)
        requires x < y
        requires ms == funcRange(f, x, y)
        requires isBounded(f, x, y)
        requires inf(ms, m)
        ensures InfWidth(f, x, y, funcRange(f, x, y)) == prod(m,(y-x))
    {
        var M :| M > 0.0 && isBoundedBetween(f,x,y,M);
        var q := f(x);
        assert q in ms;
        BoundedBelow(f, x, y, x, y, M);
        infimumInfSame(ms, q, -M, m);
    }

    ghost predicate MidInfWidthLessThan(f: real -> real, x: real, y: real, a: real, b: real, m: real ) 
        requires a <= x < y <= b
        requires isBounded(f, x, y)
    {
        prod(m,(y-x)) <= InfWidth(f, x, y, funcRange(f, x, y))
    }

    lemma InfOfAllLessThanSome(f: real -> real, a: real, b: real, x: real, y: real, ms: iset<real>, m: real)
        requires x < y
        requires a < b
        requires a <= x < y <=b
        requires ms == funcRange(f, a, b)
        requires isBounded(f, x, y)
        requires inf(ms, m)
        ensures  MidInfWidthLessThan(f, x, y, a, b, m)
    {
        var fs := funcRange(f, x, y);
        var q := f(x);
        assert q in fs;
        var M :| M > 0.0 && isBoundedBetween(f,x,y,M);
        BoundedBelow(f, x, y, x, y, M);
        CompletenessAxiomLower(fs, -M);
        var m_0 :| inf(fs, m_0);
        calc {
            InfWidth(f, x, y, funcRange(f, x, y));
            prod(infimum(funcRange(f, x, y), q, -M),(y-x));
            {infAllUnique(fs, m_0);}
            m_0*(y-x);
        }
        assert m <= m_0 by {

                assert fs <= funcRange(f, a, b);
                if m_0 < m {
                    assert lowerBound(fs, m);
                    assert lowerBound(fs, m_0);
                    assert lowerBound(funcRange(f, x, y), m_0);
                    var diff := m - m_0;
                    assert diff > 0.0;
                    var epsilon := diff / 2.0;
                    assert !lowerBound(fs, add(m_0, epsilon));
                    assert false;
                }
        }
        prodLessThan(m, y-x, m_0);
        assert m*(y-x) <= m_0*(y-x);
    }

    ghost function LowerSumAlt(f: real -> real, P: Partition, a: real, b: real): real 
        requires a < b
        requires isBounded(f, a, b)
        requires |P.xs| > 1
        requires PartitionOf(a,b, P)
        decreases |P.xs|
    {
        // var ms := funcRange(f, P.xs[0], P.xs[1]);
        // var q := f(P.xs[0]);
        // assert q in ms;
        // var M :| M > 0.0 && isBoundedBetween(f,a,b,M);
        // assert P.xs[0] in P.xs;
        // BoundedBelow(f, a, b, P.xs[0], P.xs[1], M);
        // var m_0 := infimum(ms, q, -M);
        // var res := m_0*(P.xs[1]-P.xs[0]);
        if |P.xs| == 2 then InfWidth(f, P.xs[0], P.xs[1], funcRange(f, P.xs[0], P.xs[1])) else
        functionBoundedInMiddle(f, a, b, P.xs[1]);
        InfWidth(f, P.xs[0], P.xs[1], funcRange(f, P.xs[0], P.xs[1])) + LowerSumAlt(f, Partition(P.xs[1..], P.s - {P.xs[0]}), P.xs[1], b)
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

    lemma LowerSumAssociative(f: real -> real, P_1: Partition, P_2: Partition, P_3: Partition, a: real, b: real, c: real, d: real)
        requires a < b < c < d
        requires isBounded(f, a, d)
        requires isBounded(f, a, b)
        requires isBounded(f, b, c)
        requires isBounded(f, c, d)
        requires PartitionOf(a,b, P_1)
        requires PartitionOf(b,c, P_2)
        requires PartitionOf(c,d, P_3)
        ensures LowerSumAlt(f, P_1, a, b) + (LowerSumAlt(f, P_2, b, c) + LowerSumAlt(f, P_3, c, d)) == (LowerSumAlt(f, P_1, a, b) + LowerSumAlt(f, P_2, b, c)) + LowerSumAlt(f, P_3, c, d)
        {

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
        ensures LowerSumAlt(f, P, a, b) == LowerSumAlt(f, P_1, a, c) + LowerSumAlt(f, P_2, c, b)
        // decreases |P.xs|
    // {
    //     assert P_1.xs[|P_1.xs|-1] == c;
    //     assert P_1.xs[0] == a;
    //     assert P_2.xs[0] == c;
    //     assert P_2.xs[|P_2.xs|-1] == b;
    //     if |P_1.xs| == 2 {
    //         var ms := funcRange(f, P_1.xs[0], P_1.xs[1]);
    //         var ms' := funcRange(f, P.xs[0], P.xs[1]);
    //         assert ms == ms';
    //         var q := f(P_1.xs[0]);
    //         var q' := f(P.xs[0]);
    //         assert q in ms;
    //         assert q' in ms';
    //         var M :| M > 0.0 && isBoundedBetween(f,a,b,M);
    //         BoundedBelow(f, a, b, P_1.xs[0], P_1.xs[1], M);
    //         var m_0 := infimum(ms, q, -M);
    //         var m_0' := infimum(ms', q', -M);
    //         infAllUnique(ms, m_0);
    //         infAllUnique(ms', m_0');
    //         calc {
    //             LowerSumAlt(f, P_1, a, c);
    //             m_0*(P_1.xs[1]-P_1.xs[0]);
    //         }
    //         assert P.xs[0] == P_1.xs[0];
    //         assert P.xs[1] == P_1.xs[1];
    //         assert P_2 == Partition(P.xs[1..], P.s - {P.xs[0]});
    //         // calc {
    //         //     LowerSumAlt(f, P, a, b);
    //         //     m_0'*(P.xs[1]-P.xs[0]) + LowerSumAlt(f, Partition(P.xs[1..], P.s - {P.xs[0]}), P.xs[1], b);
    //         // }
    //         assume LowerSumAlt(f, P, a, b) == m_0*(P_1.xs[1]-P_1.xs[0]) + LowerSumAlt(f, Partition(P.xs[1..], P.s - {P.xs[0]}), P.xs[1], b);
    //         assert LowerSumAlt(f, Partition(P.xs[1..], P.s - {P.xs[0]}), P.xs[1], b) == LowerSumAlt(f, P_2, c, b);
    //         // // assert LowerSumAlt(f, P_2, c, b) == LowerSumAlt(f, P, a, b);
    //         assert LowerSumAlt(f, P, a, b) == LowerSumAlt(f, P_1, a, c) + LowerSumAlt(f, P_2, c, b);
    //     } else {
    //         var c' := P_1.xs[1];
    //         assert c' != c && c' < c;
    //         functionBoundedInMiddle(f, a, c, c');
    //         assert P_1.xs[1..][0] == c';
    //         assert P_1.xs[1..][|P_1.xs[1..]|-1] == c;
    //         LowerSumConcat2(f, P_1, Partition(P_1.xs[..2], {P_1.xs[0], P_1.xs[1]}), Partition(P_1.xs[1..], P_1.s - {P_1.xs[0]}), a, c, c');

    //         var ms := funcRange(f, P_1.xs[0], P_1.xs[1]);
    //         var q := f(P_1.xs[0]);
    //         assert q in ms;
    //         var M :| M > 0.0 && isBoundedBetween(f,a,b,M);
    //         BoundedBelow(f, a, b, P_1.xs[0], P_1.xs[1], M);
    //         var m_0 := infimum(ms, q, -M);
    //         infAllUnique(ms, m_0);
    //         calc {
    //             LowerSumAlt(f, Partition(P_1.xs[..2], {P_1.xs[0], P_1.xs[1]}), a, P_1.xs[1]);
    //             m_0*(P_1.xs[1]-P_1.xs[0]);
    //         }
    //         assert Partition(P.xs[1..], P.s - {P.xs[0]}) == Partition(P_1.xs[..|P_1.xs|-1][1..]+P_2.xs, P_1.s + P_2.s - {P_1.xs[0]});
    //         assert LowerSumAlt(f, P_1, a, c) == LowerSumAlt(f, Partition(P_1.xs[..2], {P_1.xs[0], P_1.xs[1]}), a, P_1.xs[1]) + LowerSumAlt(f, Partition(P_1.xs[1..], P_1.s - {P_1.xs[0]}), P_1.xs[1], c);
    //         LowerSumConcat2(f, Partition(P.xs[1..], P.s - {P.xs[0]}), Partition(P_1.xs[1..], P_1.s - {P_1.xs[0]}), P_2, P_1.xs[1], b, c);
    //         assert LowerSumAlt(f, P, a, b) == LowerSumAlt(f, P_1, a, c) + LowerSumAlt(f, P_2, c, b);
    //     }
    // }

    // lemma {:verify false} LowerSumPartial(f: real -> real, P: Partition, a: real, b: real, i: nat, m_i: real)
    //     requires a < b
    //     requires f in BoundedFunctions(a, b)
    //     requires PartitionOf(a,b, P)
    //     requires 1 <= i < |P.xs|-1
    //     requires inf(funcRange(f, P.xs[i-1], P.xs[i]), m_i)
    //     ensures LowerSum(f, P, a, b) == m_i * (P.xs[i] - P.xs[i-1]) + LowerSum(f, PartitionRemoveIndex(P, a, b, i), a, b)
    // {
    //     if |P.xs| == 2 {
    //         assert LowerSum(f, P, a, b) == m_i * (P.xs[i] - P.xs[i-1]);
    //     } else {
    //         var l := LowerSum(f, P, a, b);
    //         var l' := m_i * (P.xs[i] - P.xs[i-1]) + LowerSum(f, PartitionRemoveIndex(P, a, b, i), a, b);
    //         assert l == l';
    //     }
    //     //var l := LowerSum(f, P, a, b);
    // }


    // ghost function UpperSum(f: real -> real, P: Partition, a: real, b: real): real 
    //     requires a < b
    //     requires f in BoundedFunctions(a, b)
    //     requires PartitionOf(a,b, P)
    // {
    //     UpperSumHelper(f, P, a, b, 1)
    // }

    // ghost function UpperSumHelper(f: real -> real, P: Partition, a: real, b: real, i: nat): real 
    //     requires a < b
    //     requires f in BoundedFunctions(a, b)
    //     requires PartitionPartial(a,b, P)
    //     requires 1 <= i < |P.xs|
    //     decreases |P.xs|-i
    // {
    //     var ms := iset x | P.xs[i-1] <= x <= P.xs[i] :: f(x);
    //     var q := f(P.xs[i-1]);
    //     assert q in ms;
    //     var M :| M > 0.0 && isBoundedBetween(f,a,b,M);
    //     assert P.xs[i-1] in P.xs;
    //     BoundedAbove(f, a, b, P.xs[i-1], P.xs[i], M);
    //     CompletenessAxiomUpper(ms, M);
    //     var M_i :| sup(ms, M_i);
    //     if i == |P.xs|-1 then M_i * (P.xs[i] - P.xs[i-1]) else M_i * (P.xs[i] - P.xs[i-1]) + UpperSumHelper(f, P, a, b, i+1)
    // }

    ghost function UpperSumAlt(f: real -> real, P: Partition, a: real, b: real): real 
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
        BoundedAbove(f, a, b, P.xs[0], P.xs[1], M);
        var M_0 := supremum(ms, q, M);
        var res := M_0*(P.xs[1]-P.xs[0]);
        if |P.xs| == 2 then res else res + UpperSumAlt(f, Partition(P.xs[1..], P.s - {P.xs[0]}), a, b)
    }

    lemma {:verify false} AllPartitionSetBoundedLow(f: real -> real, a: real, b: real, M: real,  P: Partition)
        requires a < b
        requires M > 0.0
        requires isBoundedBetween(f, a, b, M)
        requires PartitionOf(a,b, P)
        // requires sup(funcRange(f, a, b), fsup)
        ensures LowerSumAlt(f, P, a, b) <= prod(sub(b,a), M)
        decreases |P.xs|
    {
        if |P.xs| < 2 {
            assert false;

        } else if |P.xs| == 2 {
            assert P.xs[0] == a;
            assert P.xs[1] == b;
            var iw := InfWidth(f, P.xs[0], P.xs[1], funcRange(f, P.xs[0], P.xs[1]));
            var m_0 :| inf(funcRange(f, P.xs[0], P.xs[1]), m_0);
            calc {
                LowerSumAlt(f, P, a, b);
                InfWidth(f, P.xs[0], P.xs[1], funcRange(f, P.xs[0], P.xs[1]));
                prod(m_0,sub(P.xs[1],P.xs[0]));
                m_0*sub(P.xs[1],P.xs[0]);
            }
            assert (P.xs[1]-P.xs[0]) == (b-a);
            assume m_0 <= M;
            prodLessThan(m_0, sub(b,a), M);
            assert ablte(m_0, sub(b,a), M);
            assert prod(m_0,sub(b,a)) <= prod(M,sub(b,a));
            assert m_0*(b-a) <= M*(b-a);
            // assert InfWidth(f, P.xs[0], P.xs[1], funcRange(f, P.xs[0], P.xs[1])) <= (b-a) * M;
            // assert LowerSumAlt(f, P, a, b) <= (b-a) * M;
            // assert LowerSumAlt(f, P, a, b) <= prod((b-a), M);
            assert LowerSumAlt(f, P, a, b) <= prod(sub(b,a), M);
        }else{
            assert |P.xs| > 2;
            var P_First := Partition(P.xs[..2], {P.xs[0], P.xs[1]});
            var P_next := Partition(P.xs[1..], P.s - {P.xs[0]});
            assert P_next.xs[|P_next.xs|-1] == b;
            assert a < P.xs[1] < b;
            functionBoundedInMiddle(f, a, b, P.xs[1]);
            LowerSumConcat(f, P, P_First, P_next, a, b, P.xs[1]);

            var iw := InfWidth(f, P.xs[0], P.xs[1], funcRange(f, P.xs[0], P.xs[1]));
            var m_0 :| inf(funcRange(f, P.xs[0], P.xs[1]), m_0);
            calc {
                LowerSumAlt(f, P, a, b);
                InfWidth(f, P.xs[0], P.xs[1], funcRange(f, P.xs[0], P.xs[1])) + LowerSumAlt(f, P_next, P.xs[1], b);
                prod(m_0,(P.xs[1]-P.xs[0])) + LowerSumAlt(f, P_next, P.xs[1], b);
                prod(m_0 , sub(P.xs[1],P.xs[0])) + LowerSumAlt(f, P_next, P.xs[1], b);
            }
            assume m_0 <= M;
            prodLessThan(m_0, sub(P.xs[1],P.xs[0]), M);
            assert ablte(m_0, P.xs[1]-P.xs[0], M);
            assert prod(m_0,(P.xs[1]-P.xs[0])) <= prod(M,(P.xs[1]-P.xs[0]));
            assert m_0*(P.xs[1]-P.xs[0]) <= M*(P.xs[1]-P.xs[0]);

            var ms_rest := funcRange(f, P.xs[1], b);
            var q_rest := f(P.xs[1]);
            assert q_rest in ms_rest;
            assert P.xs[1] in P_next.xs;
            assert forall x :: P.xs[1] <= x <= b ==> f.requires(x);
            BoundedBelow(f, a, b, P.xs[1], b, M);
            var m_rest := infimum(ms_rest, q_rest, -M);
            AllPartitionSetBoundedLow(f, P.xs[1], b, M, P_next);
            assert LowerSumAlt(f, P_next, P.xs[1], b) <= prod(sub(b,P.xs[1]), M);
            // assert LowerSumAlt(f, P_next, P.xs[1], b) <= (b-P.xs[1]) * M;
            assert M*(P.xs[1]-P.xs[0]) + (b-P.xs[1])*M == M*(b-a);
            // assert m_0*(P.xs[1]-P.xs[0]) + LowerSumAlt(f, P_next, P.xs[1], b) <= M*(P.xs[1]-P.xs[0]) + (b-P.xs[1])*M == M*(b-a);
            // assert m_0*(P.xs[1]-P.xs[0]) + LowerSumAlt(f, P_next, P.xs[1], b) <=  M*(b-a);
            // assert LowerSumAlt(f, P, a, b) <= (b-a) * M;
            assert LowerSumAlt(f, P, a, b) <= prod((b-a) , M);
            assert LowerSumAlt(f, P, a, b) <= prod(sub(b,a) , M);
        }
        assert LowerSumAlt(f, P, a, b) <= prod(sub(b,a) , M);
    }

    lemma  {:verify false} AllPartitionSetBoundedUpper(f: real -> real, a: real, b: real, M: real, P: Partition)
        requires a < b
        requires M > 0.0
        requires isBoundedBetween(f, a, b, M)
        requires PartitionOf(a,b, P)
        ensures UpperSumAlt(f, P, a, b) >= (b-a) * -M
    {}


    ghost function LowerIntegral(f: real -> real, a: real, b: real): real 
        requires a < b
        requires isBounded(f, a, b)
    {
        var M :| M > 0.0 && isBoundedBetween(f,a,b,M);
        var allPartitions := iset P | PartitionOf(a,b, P);
        var allPartitionSums := iset P | P in allPartitions :: LowerSumAlt(f, P, a, b);
        var canonical_P := Partition([a, b], {a, b});
        var x := LowerSumAlt(f, canonical_P, a, b);
        assert x in allPartitionSums;
        assert forall sum :: sum in allPartitionSums ==> sum <= prod((b-a),M) by {
            forall sum | sum in allPartitionSums
                ensures sum <= prod((b-a),M)
            {
                var P :| P in allPartitions && sum == LowerSumAlt(f, P, a, b);
                AllPartitionSetBoundedLow(f, a, b, M,  P);
            }
        }
        assert upperBound(allPartitionSums, prod(sub(b,a),M));
        CompletenessAxiomUpper(allPartitionSums, (b-a)*M);
        var fsup :| sup(allPartitionSums, fsup);
        
       supremum(allPartitionSums, x,  (b-a)*M)
    }

    ghost function UpperIntegral(f: real -> real, a: real, b: real): real 
        requires a < b
        requires isBounded(f, a, b)
    {
        var M :| M > 0.0 && isBoundedBetween(f,a,b,M);
        var allPartitions := iset P | PartitionOf(a,b, P);
        var allPartitionSums := iset P | P in allPartitions :: UpperSumAlt(f, P, a, b);
        var canonical_P := Partition([a, b], {a, b});
        var x := UpperSumAlt(f, canonical_P, a, b);
        assert forall sum :: sum in allPartitionSums ==> sum >= (b-a)*-M by {
            forall sum | sum in allPartitionSums
                ensures sum >= (b-a)*-M
            {
                var P :| P in allPartitions && sum == UpperSumAlt(f, P, a, b);
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
        ensures prod(m, sub(b,a)) <= LowerSumAlt(f, P, a, b) <= UpperSumAlt(f, P, a, b) <= prod(M,sub(b,a))
    {
        Prop_zero_one_six_inf(f, P, a, b, m);
        Prop_zero_one_six_lower_upper(f, P, a, b);
        Prop_zero_one_six_sup(f, P, a, b, M);
    }

    predicate ablte(a: real, b: real, a': real)
    {
        prod(a,b) <= prod(a',b)
    }

    lemma prodLessThan(a: real, b: real, a': real)
        requires a <= a'
        requires b > 0.0
        ensures ablte(a, b, a')
    {
    }

    lemma subAdds(a: real, b: real, x: real) 
        requires a < x < b
        ensures sub(b, a) == sub(b, x) + sub(x, a)
    {}

    lemma prodEqualsSilly(m: real, a: real, b: real, x: real)
        requires a < x < b
        ensures prod(m, sub(b, a)) == prod(m, sub(b, x) + sub(x, a))
    {
        subAdds(a, b, x);
    }


    lemma Prop_zero_one_six_inf(f: real -> real, P: Partition, a: real, b: real, m: real)
        requires a < b
        requires isBounded(f, a, b)
        requires PartitionOf(a,b, P)
        requires inf(funcRange(f, a, b), m)
        ensures prod(m,sub(b,a)) <= LowerSumAlt(f, P, a, b)
        decreases |P.xs|
    {
        var l := LowerSumAlt(f, P, a, b);
        // if P.xs == [a, b] {
        if |P.xs| == 2 {
            assert |P.xs| == 2;
            assert P.xs[0] == a;
            assert P.xs[1] == b;
            infAllUnique(funcRange(f, P.xs[0], P.xs[1]), m);
            var ms := funcRange(f, P.xs[0], P.xs[1]);
            var q := f(P.xs[0]);
            assert q in ms;
            var M :| M > 0.0 && isBoundedBetween(f,a,b,M);
            assert P.xs[0] in P.xs;
            BoundedBelow(f, a, b, P.xs[0], P.xs[1], M);
            var m_0 := infimum(ms, q, -M);
            calc {
                LowerSumAlt(f, P, a, b);
                prod(m_0,sub(P.xs[1],P.xs[0]));
            }
            assert m == m_0 by {
                assert inf(ms, m);
                assert inf(ms, m_0);
            }
            assert prod(m,sub(b,a)) <= l;
        } else {
            var P_First := Partition(P.xs[..2], {P.xs[0], P.xs[1]});
            var P_next := Partition(P.xs[1..], P.s - {P.xs[0]});
            assert a < P.xs[1] < b;
            functionBoundedInMiddle(f, a, b, P.xs[1]);
            LowerSumConcat(f, P, P_First, P_next, a, b, P.xs[1]);
            assert LowerSumAlt(f, P, a, b) == LowerSumAlt(f, P_First, a, P.xs[1]) + LowerSumAlt(f, P_next, P.xs[1], b);
            calc {
                LowerSumAlt(f, P, a, b);
                InfWidth(f, P.xs[0], P.xs[1], funcRange(f, P.xs[0], P.xs[1])) + LowerSumAlt(f, P_next, P.xs[1], b);
            }
            assert P.xs[0] == P_First.xs[0];
            assert P.xs[1] == P_First.xs[1];
            calc {
                LowerSumAlt(f, P_First, a, P.xs[1]);
                InfWidth(f, P_First.xs[0], P_First.xs[1], funcRange(f, P_First.xs[0], P_First.xs[1]));
                InfWidth(f, P.xs[0], P.xs[1], funcRange(f, P.xs[0], P.xs[1]));
            }

            var ms := funcRange(f, P.xs[1], b);
            var q := f(P.xs[1]);
            assert q in ms;
            var M :| M > 0.0 && isBoundedBetween(f,a,b,M);
            assert P.xs[1] in P_next.xs;
            assert forall x :: P.xs[1] <= x <= b ==> f.requires(x);
            BoundedBelow(f, a, b, P.xs[1], b, M);
            var m_rest := infimum(ms, q, -M);
            Prop_zero_one_six_inf(f, P_next, P.xs[1], b, m_rest);
            assert prod(m_rest, sub(b,P.xs[1])) <= LowerSumAlt(f, P_next, P.xs[1], b);
            calc {
                l;
                InfWidth(f, P.xs[0], P.xs[1], funcRange(f, P.xs[0], P.xs[1])) + LowerSumAlt(f, P_next, P.xs[1], b);
            }

            assert m_rest >= m by {
                assert ms <= funcRange(f, a, b);
                if m_rest < m {
                    assert lowerBound(ms, m);
                    assert lowerBound(ms, m_rest);
                    assert lowerBound(funcRange(f, a, b), m_rest);
                    var diff := m - m_rest;
                    assert diff > 0.0;
                    var epsilon := diff / 2.0;
                    assert !lowerBound(ms, add(m_rest, epsilon));

                    assert false;
                }
            }
            assert b-P.xs[1] > 0.0;
            prodLessThan(m, b-P.xs[1], m_rest);
            InfOfAllLessThanSome(f, a, b, P.xs[0], P.xs[1], funcRange(f,a,b), m);
            assert MidInfWidthLessThan(f, P.xs[0], P.xs[1], a, b, m);
            assert prod(m , sub(b,a)) == prod(m, sub(P.xs[1], P.xs[0])) + prod(m, sub(b, P.xs[1])) by {
                assert P.xs[0] == a;
                assert sub(b,a) == sub(P.xs[1], P.xs[0]) + sub(b, P.xs[1]);
                calc {
                    prod(m, sub(P.xs[1], P.xs[0])) + prod(m, sub(b, P.xs[1]));
                    {ProdDistributesOverSum(m, sub(P.xs[1], P.xs[0]), sub(b, P.xs[1]));}
                    prod(m, sub(P.xs[1], P.xs[0]) + sub(b, P.xs[1]));
                    {prodEqualsSilly(m, a, b, P.xs[1]);}
                    prod(m, sub(b,a));
                }
            }
            assert prod(m,sub(P.xs[1],P.xs[0])) + prod(m,sub(b,P.xs[1])) <= prod(m,sub(P.xs[1],P.xs[0])) + prod(m_rest,sub(b,P.xs[1])) by {
                var diff := m_rest - m;
                assert diff >= 0.0;
                assert m_rest == m + diff;
                calc {
                    prod(m, sub(P.xs[1],P.xs[0])) + prod(m_rest, sub(b,P.xs[1]));
                    prod(m, sub(P.xs[1],P.xs[0])) + prod(m+diff,sub(b,P.xs[1]));
                    {ProdDistributesOverSum2(m, diff, sub(b,P.xs[1]));}
                    prod(m, sub(P.xs[1],P.xs[0])) + prod(m, sub(b,P.xs[1])) + prod(diff,sub(b,P.xs[1]));
                    prod(m, sub(b,a)) + prod(diff,sub(b,P.xs[1]));
                }
                assert prod(m,sub(P.xs[1],P.xs[0])) + prod(m,sub(b,P.xs[1])) == prod(m,sub(b,a));
                assert prod(m, sub(b,a)) <= prod(m, sub(b,a)) + prod(diff,sub(b,P.xs[1]));
            }
            assert prod(m,sub(P.xs[1],P.xs[0])) + prod(m_rest,sub(b,P.xs[1])) <= InfWidth(f, P.xs[0], P.xs[1], funcRange(f, P.xs[0], P.xs[1])) + LowerSumAlt(f, P_next, P.xs[1], b);
            assert prod(m,sub(b,a)) <= l;
        }
    }

    lemma {:verify false} Prop_zero_one_six_sup(f: real -> real, P: Partition, a: real, b: real, M: real)
        requires a < b
        requires f in BoundedFunctions(a, b)
        requires PartitionOf(a,b, P)
        requires sup(funcRange(f, a, b), M)
        ensures UpperSumAlt(f, P, a, b) <= prod(M, sub(b,a))
    {
        var u := UpperSumAlt(f, P, a, b);
        assert u <= M*(b-a);
    }

    lemma {:verify false} Prop_zero_one_six_lower_upper(f: real -> real, P: Partition, a: real, b: real)
        requires a < b
        requires f in BoundedFunctions(a, b)
        requires PartitionOf(a,b, P)
        ensures LowerSumAlt(f, P, a, b) <= UpperSumAlt(f, P, a, b)
    {
        var l := LowerSumAlt(f, P, a, b);
        var u := UpperSumAlt(f, P, a, b);
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

    lemma {:verify } {:vcs_split_on_every_assert} Problem5a(f: real -> real, a: real, b: real, c: real) returns (g: real -> real)
        requires a < b
        requires a <= c <= b
        requires isBounded(f, a, b)
        requires RiemannIntegrable(f, a, b)
        ensures forall x :: a <= x <= b && x != c ==> f(x) == g(x)
        ensures RiemannIntegrable(g, a, b)
    {
        var Gc: real :| true;
        g := (x: real) => if x == c then Gc else f(x);
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
        return g;
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

    lemma {:verify } Problem5b(f: real -> real, a: real, b: real, diffpoints: set<real>) returns  (g: real -> real)
        requires a < b
        requires forall c :: c in diffpoints ==> a <= c <= b
        requires isBounded(f, a, b)
        requires RiemannIntegrable(f, a, b)
        ensures forall x :: a <= x <= b && x !in diffpoints ==> f(x) == g(x)
        ensures RiemannIntegrable(g, a, b)
    {
        if |diffpoints| == 0 {
            return f;
        } else if |diffpoints| == 1 {
            assert diffpoints != {};
            var c :| c in diffpoints;
            assert diffpoints == {c} by {
                assert |diffpoints| == 1;
                assert |diffpoints - {c}| == 0;
                assert diffpoints - {c} == {};
            }
            g := Problem5a(f,  a, b, c);
            assert RiemannIntegrable(g, a, b);
            return g;
        } else {
            var c :| c in diffpoints;
            var g' := Problem5b(f, a, b, diffpoints-{c});
            var gc: real :| true;
            g := (x: real) => if x == c then gc else g'(x);
            assert isBounded(g', a, b);
            var M' :| M' > 0.0 && isBoundedBetween(g', a, b, M');
            var M := if M' > abs(gc) then M' else abs(gc);
            assert forall x :: a <= x <= b && x !in diffpoints ==> f(x) == g(x);
            assert isBounded(g, a, b) by {
                forall x | a <= x <= b
                    ensures g.requires(x)
                    ensures abs(g(x)) <= M
                {
                    if x == c {
                        assert abs(gc) <= M;
                        assert abs(g(x)) <= M;
                    } else {
                        assert g'(x) == g(x);
                        assert g'.requires(x);
                        assert abs(g'(x)) <= M';
                        assert abs(g(x)) <= M;
                    }
                }
                assert isBoundedBetween(g, a, b, M);
            }
            assume LowerIntegral(g, a, b) == UpperIntegral(g, a, b);
            assert RiemannIntegrable(g, a, b);
            return g;
        }
    }
}

