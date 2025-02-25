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

    ghost function SupWidth(f: real -> real, x: real, y: real, ms: iset<real>): real 
        requires x < y
        requires ms == funcRange(f, x, y)
        requires isBounded(f, x, y)
        ensures exists i_a :: sup(ms, i_a)
        ensures forall i_b :: sup(ms, i_b) ==> SupWidth(f, x, y, ms) == prod(i_b, sub(y,x)) 
    {
        var q := f(x);
        assert q in ms;
        var M :| M > 0.0 && isBoundedBetween(f,x,y,M);
        BoundedAbove(f, x, y, x, y, M);
        supAllUnique(ms, supremum(ms, q, M));
        prod(supremum(ms, q, M),sub(y,x))
    }

    ghost predicate MidInfWidthLessThan(f: real -> real, x: real, y: real, a: real, b: real, m: real ) 
        requires a <= x < y <= b
        requires isBounded(f, x, y)
    {
        prod(m,(y-x)) <= InfWidth(f, x, y, funcRange(f, x, y))
    }

    lemma SupWidthGTEInfWidth(f: real -> real, x: real, y: real, ms: iset<real>)
        requires x < y
        requires ms == funcRange(f, x, y)
        requires isBounded(f, x, y)
        ensures  SupWidth(f, x, y, funcRange(f, x, y)) >= InfWidth(f, x, y, funcRange(f, x, y))
    {
        var sw := SupWidth(f, x, y, ms);
        var iw := InfWidth(f, x, y, ms);
        var s1 :| sup(ms, s1);
        var i1 :| inf(ms, i1);
        calc {
            SupWidth(f, x, y, ms);
            prod(s1, sub(y,x));
        }

        calc {
            InfWidth(f, x, y, ms);
            prod(i1, sub(y,x));
        }
        assume s1 >= i1;
        prodLessThan(i1, sub(y,x), s1);
        assert prod(s1, sub(y,x)) >= prod(i1, sub(y,x));
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

    ghost function LowerSum(f: real -> real, P: Partition, a: real, b: real): real 
        requires a < b
        requires isBounded(f, a, b)
        requires |P.xs| > 1
        requires PartitionOf(a,b, P)
        decreases |P.xs|
    {
        if |P.xs| == 2 then InfWidth(f, P.xs[0], P.xs[1], funcRange(f, P.xs[0], P.xs[1])) else
        functionBoundedInMiddle(f, a, b, P.xs[1]);
        InfWidth(f, P.xs[0], P.xs[1], funcRange(f, P.xs[0], P.xs[1])) + LowerSum(f, Partition(P.xs[1..], P.s - {P.xs[0]}), P.xs[1], b)
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
        ensures LowerSum(f, P_1, a, b) + (LowerSum(f, P_2, b, c) + LowerSum(f, P_3, c, d)) == (LowerSum(f, P_1, a, b) + LowerSum(f, P_2, b, c)) + LowerSum(f, P_3, c, d)
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
        ensures LowerSum(f, P, a, b) == LowerSum(f, P_1, a, c) + LowerSum(f, P_2, c, b)
        decreases |P.xs|
    {
        assert P_1.xs[|P_1.xs|-1] == c;
        assert P_1.xs[0] == a;
        assert P_2.xs[0] == c;
        assert P_2.xs[|P_2.xs|-1] == b;
        if |P_1.xs| == 2 {
            assert P.xs[0] == P_1.xs[0];
            assert P.xs[1] == P_1.xs[1];
            assert P_2 == Partition(P.xs[1..], P.s - {P.xs[0]});
            assert LowerSum(f, Partition(P.xs[1..], P.s - {P.xs[0]}), P.xs[1], b) == LowerSum(f, P_2, c, b);
            var d0 := InfWidth(f, P_1.xs[0], P_1.xs[1], funcRange(f, P_1.xs[0], P_1.xs[1]));
            var d1 := InfWidth(f, P.xs[0], P.xs[1], funcRange(f, P.xs[0], P.xs[1]));
            assert d0 == d1;
            calc {
                LowerSum(f, P, a, b);
                d1 + LowerSum(f, Partition(P.xs[1..], P.s - {P.xs[0]}), P.xs[1], b);
                d0 + LowerSum(f, Partition(P.xs[1..], P.s - {P.xs[0]}), P.xs[1], b);
                LowerSum(f, P_1, a, c) + LowerSum(f, Partition(P.xs[1..], P.s - {P.xs[0]}), P.xs[1], b);
            }
            assert LowerSum(f, P, a, b) == LowerSum(f, P_1, a, c) + LowerSum(f, P_2, c, b);
        } else {
            var c' := P_1.xs[1];
            assert c' != c && c' < c;
            functionBoundedInMiddle(f, a, c, c');
            functionBoundedInMiddle(f, a, b, c');
            //assert P_1.xs[1..][0] == c';
            //assert P_1.xs[1..][|P_1.xs[1..]|-1] == c;
            var P_next := Partition(P.xs[1..], P.s - {P.xs[0]});
            assert P_next == Partition(P_1.xs[..|P_1.xs|-1][1..]+P_2.xs, P_1.s+P_2.s-{P_1.xs[0]}) by {
                assert P_1.s + P_2.s - {P_1.xs[0]} == P.s  - {P.xs[0]};
                assert P_1.xs[..|P_1.xs|-1][1..] + P_2.xs == P_next.xs;
            }
            var P_1_next := Partition(P_1.xs[1..], P_1.s - {P_1.xs[0]});
            var d0 := InfWidth(f, P_1.xs[0], P_1.xs[1], funcRange(f, P_1.xs[0], P_1.xs[1]));
            var d1 := InfWidth(f, P.xs[0], P.xs[1], funcRange(f, P.xs[0], P.xs[1]));
            assert d0 == d1;
            LowerSumConcat(f,P_next, P_1_next, P_2, c', b, c);
            calc {
                LowerSum(f, P, a, b);
                d1 + LowerSum(f, P_next, P.xs[1], b);
                d0 + LowerSum(f, P_next, P.xs[1], b);
                d0 + LowerSum(f, P_1_next, c', c) + LowerSum(f, P_2, c, b);
                LowerSum(f, P_1, a, c) + LowerSum(f, P_2, c, b);
            }
            assert LowerSum(f, P, a, b) == LowerSum(f, P_1, a, c) + LowerSum(f, P_2, c, b);
        }
    }

    lemma UpperSumConcat(f: real -> real, P: Partition, P_1: Partition, P_2: Partition, a: real, b: real, c: real)
        requires a < c < b
        requires isBounded(f, a, b)
        requires isBounded(f, a, c)
        requires isBounded(f, c, b)
        requires PartitionOf(a,c, P_1)
        requires PartitionOf(c,b, P_2)
        requires P == Partition(P_1.xs[..|P_1.xs|-1]+P_2.xs, P_1.s+P_2.s)
        requires PartitionOf(a,b, P)
        ensures UpperSum(f, P, a, b) == UpperSum(f, P_1, a, c) + UpperSum(f, P_2, c, b)
        decreases |P.xs|
    {
        assert P_1.xs[|P_1.xs|-1] == c;
        assert P_1.xs[0] == a;
        assert P_2.xs[0] == c;
        assert P_2.xs[|P_2.xs|-1] == b;
        if |P_1.xs| == 2 {
            assert P.xs[0] == P_1.xs[0];
            assert P.xs[1] == P_1.xs[1];
            assert P_2 == Partition(P.xs[1..], P.s - {P.xs[0]});
            var d0 := SupWidth(f, P_1.xs[0], P_1.xs[1], funcRange(f, P_1.xs[0], P_1.xs[1]));
            var d1 := SupWidth(f, P.xs[0], P.xs[1], funcRange(f, P.xs[0], P.xs[1]));
            assert d0 == d1;
            calc {
                UpperSum(f, P, a, b);
                d1 + UpperSum(f, Partition(P.xs[1..], P.s - {P.xs[0]}), P.xs[1], b);
                d0 + UpperSum(f, Partition(P.xs[1..], P.s - {P.xs[0]}), P.xs[1], b);
            }
            assert UpperSum(f, P, a, b) == UpperSum(f, P_1, a, c) + UpperSum(f, P_2, c, b);
        } else {
            var c' := P_1.xs[1];
            assert c' != c && c' < c;
            functionBoundedInMiddle(f, a, c, c');
            functionBoundedInMiddle(f, a, b, c');
            //assert P_1.xs[1..][0] == c';
            //assert P_1.xs[1..][|P_1.xs[1..]|-1] == c;
            var P_next := Partition(P.xs[1..], P.s - {P.xs[0]});
            assert P_next == Partition(P_1.xs[..|P_1.xs|-1][1..]+P_2.xs, P_1.s+P_2.s-{P_1.xs[0]}) by {
                assert P_1.s + P_2.s - {P_1.xs[0]} == P.s  - {P.xs[0]};
                assert P_1.xs[..|P_1.xs|-1][1..] + P_2.xs == P_next.xs;
            }
            var P_1_next := Partition(P_1.xs[1..], P_1.s - {P_1.xs[0]});
            var d0 := SupWidth(f, P_1.xs[0], P_1.xs[1], funcRange(f, P_1.xs[0], P_1.xs[1]));
            var d1 := SupWidth(f, P.xs[0], P.xs[1], funcRange(f, P.xs[0], P.xs[1]));
            assert d0 == d1;
            UpperSumConcat(f,P_next, P_1_next, P_2, c', b, c);
            calc {
                UpperSum(f, P, a, b);
                d1 + UpperSum(f, P_next, P.xs[1], b);
                d0 + UpperSum(f, P_next, P.xs[1], b);
                d0 + UpperSum(f, P_1_next, c', c) + UpperSum(f, P_2, c, b);
                UpperSum(f, P_1, a, c) + UpperSum(f, P_2, c, b);
            }
            assert UpperSum(f, P, a, b) == UpperSum(f, P_1, a, c) + UpperSum(f, P_2, c, b);
        }
    }

    ghost function UpperSum(f: real -> real, P: Partition, a: real, b: real): real 
        requires a < b
        requires isBounded(f, a, b)
        requires |P.xs| > 1
        requires PartitionOf(a,b, P)
        decreases |P.xs|
    {
        if |P.xs| == 2 then SupWidth(f, P.xs[0], P.xs[1], funcRange(f, P.xs[0], P.xs[1])) else
        functionBoundedInMiddle(f, a, b, P.xs[1]);
        SupWidth(f, P.xs[0], P.xs[1], funcRange(f, P.xs[0], P.xs[1])) + UpperSum(f, Partition(P.xs[1..], P.s - {P.xs[0]}), P.xs[1], b)
    }

    lemma AllPartitionSetBoundedLow(f: real -> real, a: real, b: real, M: real,  P: Partition)
        requires a < b
        requires M > 0.0
        requires isBoundedBetween(f, a, b, M)
        requires PartitionOf(a,b, P)
        // requires sup(funcRange(f, a, b), fsup)
        ensures LowerSum(f, P, a, b) <= prod(M, sub(b,a))
        decreases |P.xs|
    {
        var ms := funcRange(f, a, b);
        var si := SupWidth(f, a, b, ms);
        var s :| sup(ms, s);
        var ii := InfWidth(f, a, b, ms);
        assert sup(funcRange(f, a, b), s);
        var i :| inf(ms, i);
        Prop_zero_one_six(f, P, a, b, i, s);
        assert LowerSum(f, P, a, b) <= prod(s, sub(b, a));
        SupLTEBound(f, P, a,b, M, s);
        assert s <= M;
        prodLessThan(s, sub(b,a), M);
    }

    lemma AllPartitionSetBoundedUpper(f: real -> real, a: real, b: real, M: real, P: Partition)
        requires a < b
        requires M > 0.0
        requires isBoundedBetween(f, a, b, M)
        requires PartitionOf(a,b, P)
        ensures UpperSum(f, P, a, b) >= prod(-M, sub(b,a))
    {
        var ms := funcRange(f, a, b);
        var si := SupWidth(f, a, b, ms);
        var s :| sup(ms, s);
        var ii := InfWidth(f, a, b, ms);
        assert sup(funcRange(f, a, b), s);
        var i :| inf(ms, i);
        Prop_zero_one_six(f, P, a, b, i, s);
        assert UpperSum(f, P, a, b) >= prod(i, sub(b, a));
        InfGTEBound(f, P, a,b, M, i);
        assert i >= -M;
        prodLessThan(-M, sub(b,a), i);
        assert prod(-M, sub(b,a)) <= prod(i, sub(b,a)) <= UpperSum(f, P, a, b);
    }


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
        assert forall sum :: sum in allPartitionSums ==> sum <= prod((b-a),M) by {
            forall sum | sum in allPartitionSums
                ensures sum <= prod(M, sub(b,a))
            {
                var P :| P in allPartitions && sum == LowerSum(f, P, a, b);
                AllPartitionSetBoundedLow(f, a, b, M,  P);
            }
        }
        assert upperBound(allPartitionSums, prod(sub(b,a),M));
        CompletenessAxiomUpper(allPartitionSums, prod(M, sub(b,a)));
        var fsup :| sup(allPartitionSums, fsup);
        
       supremum(allPartitionSums, x,  prod(M, sub(b,a)))
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
        assert forall sum :: sum in allPartitionSums ==> sum >= prod(-M, sub(b,a)) by {
            forall sum | sum in allPartitionSums
                ensures sum >= prod(-M, sub(b,a))
            {
                var P :| P in allPartitions && sum == UpperSum(f, P, a, b);
                AllPartitionSetBoundedUpper(f, a, b, M, P);
            }
        }
        infimum(allPartitionSums, x, prod(-M, sub(b,a)))
    }

    ghost predicate RiemannIntegrable(f: real -> real, a: real, b: real) {
        a < b && isBounded(f, a, b) && LowerIntegral(f, a, b) == UpperIntegral(f, a, b)
    }

    lemma SupLTEBound(f: real -> real, P: Partition, a: real, b: real, M: real, s: real)
        requires a < b
        requires M > 0.0
        requires isBoundedBetween(f, a, b, M)
        requires PartitionOf(a,b, P)
        requires sup(funcRange(f, a, b), s)
        ensures s <= M
    {
        if s > M {
            assert upperBound(funcRange(f, a, b), M) by {
                forall x | a <= x <= b
                ensures f.requires(x)
                ensures f(x) <= M
                {
                    assert f.requires(x);
                    assert abs(f(x)) <= M;
                }
            }
            var diff := s - M;
            assert diff > 0.0;
            assert upperBound(funcRange(f, a, b), sub(s, diff/2.0));
            assert false;
        }
    }

    lemma InfGTEBound(f: real -> real, P: Partition, a: real, b: real, M: real, i: real)
        requires a < b
        requires M > 0.0
        requires isBoundedBetween(f, a, b, M)
        requires PartitionOf(a,b, P)
        requires inf(funcRange(f, a, b), i)
        ensures i >= -M
    {
        if i < -M {
            assert lowerBound(funcRange(f, a, b), -M) by {
                forall x | a <= x <= b
                ensures f.requires(x)
                ensures f(x) >= -M
                {
                    assert f.requires(x);
                    assert abs(f(x)) >= -M;
                }
            }
            var diff := -M - i;
            assert diff > 0.0;
            assert lowerBound(funcRange(f, a, b), add(i, diff/2.0));
            assert false;
        }
    }


    lemma Prop_zero_one_six(f: real -> real, P: Partition, a: real, b: real, m: real, M: real)
        requires a < b
        requires isBounded(f, a, b)
        requires PartitionOf(a,b, P)
        requires inf(funcRange(f, a, b), m)
        requires sup(funcRange(f, a, b), M)
        ensures prod(m, sub(b,a)) <= LowerSum(f, P, a, b) <= UpperSum(f, P, a, b) <= prod(M,sub(b,a))
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
        ensures prod(m,sub(b,a)) <= LowerSum(f, P, a, b)
        decreases |P.xs|
    {
        var l := LowerSum(f, P, a, b);
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
                LowerSum(f, P, a, b);
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
            assert LowerSum(f, P, a, b) == LowerSum(f, P_First, a, P.xs[1]) + LowerSum(f, P_next, P.xs[1], b);
            calc {
                LowerSum(f, P, a, b);
                InfWidth(f, P.xs[0], P.xs[1], funcRange(f, P.xs[0], P.xs[1])) + LowerSum(f, P_next, P.xs[1], b);
            }
            assert P.xs[0] == P_First.xs[0];
            assert P.xs[1] == P_First.xs[1];
            calc {
                LowerSum(f, P_First, a, P.xs[1]);
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
            assert prod(m_rest, sub(b,P.xs[1])) <= LowerSum(f, P_next, P.xs[1], b);
            calc {
                l;
                InfWidth(f, P.xs[0], P.xs[1], funcRange(f, P.xs[0], P.xs[1])) + LowerSum(f, P_next, P.xs[1], b);
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
            assert prod(m,sub(P.xs[1],P.xs[0])) + prod(m_rest,sub(b,P.xs[1])) <= InfWidth(f, P.xs[0], P.xs[1], funcRange(f, P.xs[0], P.xs[1])) + LowerSum(f, P_next, P.xs[1], b);
            assert prod(m,sub(b,a)) <= l;
        }
    }

    lemma Prop_zero_one_six_sup(f: real -> real, P: Partition, a: real, b: real, M: real)
        requires a < b
        requires isBounded(f, a, b)
        requires PartitionOf(a,b, P)
        requires sup(funcRange(f, a, b), M)
        ensures UpperSum(f, P, a, b) <= prod(M, sub(b,a))
        decreases |P.xs|
    {
        var u := UpperSum(f, P, a, b);
        if |P.xs| == 2 {
            assert |P.xs| == 2;
            assert P.xs[0] == a;
            assert P.xs[1] == b;
            var sw := SupWidth(f, P.xs[0], P.xs[1], funcRange(f, P.xs[0], P.xs[1]));
            var m_0 :| sup(funcRange(f, P.xs[0], P.xs[1]), m_0);
            calc {
                UpperSum(f, P, a, b);
                prod(m_0,sub(P.xs[1],P.xs[0]));
            }
            assert u <= prod(M,sub(b,a));
        } else {
            var P_First := Partition(P.xs[..2], {P.xs[0], P.xs[1]});
            var P_next := Partition(P.xs[1..], P.s - {P.xs[0]});
            var si := SupWidth(f, P.xs[0], P.xs[1], funcRange(f, P.xs[0], P.xs[1]));
            var s :| sup(funcRange(f, P.xs[0], P.xs[1]), s);
            assert a < P.xs[1] < b;
            functionBoundedInMiddle(f, a, b, P.xs[1]);
            UpperSumConcat(f, P, P_First, P_next, a, b, P.xs[1]);
            assert UpperSum(f, P, a, b) == UpperSum(f, P_First, a, P.xs[1]) + UpperSum(f, P_next, P.xs[1], b);
            calc {
                UpperSum(f, P, a, b);
                SupWidth(f, P.xs[0], P.xs[1], funcRange(f, P.xs[0], P.xs[1])) + UpperSum(f, P_next, P.xs[1], b);
                prod(s, sub(P.xs[1], P.xs[0])) + UpperSum(f, P_next, P.xs[1], b);
            }
            assert P.xs[0] == P_First.xs[0] == a;
            assert P.xs[1] == P_First.xs[1];

            var ms := funcRange(f, P.xs[1], b);
            var q := f(P.xs[1]);
            assert q in ms;
            var bound :| bound > 0.0 && isBoundedBetween(f,a,b,bound);
            assert P.xs[1] in P_next.xs;
            BoundedAbove(f, a, b, P.xs[1], b, bound);
            var sup_rest := supremum(ms, q, bound);
            Prop_zero_one_six_sup(f, P_next, P.xs[1], b, sup_rest);

            assert s <= M by {
                if s > M {
                    assert funcRange(f, P.xs[0], P.xs[1]) <= funcRange(f, a, b);
                    assert upperBound(funcRange(f, a, b), M);
                    var diff := s - M;
                    assert diff > 0.0;
                    assert upperBound(funcRange(f, a, b), sub(s, diff/2.0));
                    assert false;
                }
            }
            assert sup_rest <= M by {
                if sup_rest > M {
                    assert funcRange(f, P.xs[1], b) <= funcRange(f, a, b);
                    assert upperBound(funcRange(f, a, b), M);
                    var diff := sup_rest - M;
                    assert diff > 0.0;
                    assert upperBound(funcRange(f, a, b), sub(sup_rest, diff/2.0));
                    assert false;
                }
            }
            prodLessThan(s, sub(P.xs[1],P.xs[0]), M);
            prodLessThan(sup_rest, sub(b,P.xs[1]), M);
            assert prod(M, sub(P.xs[1], P.xs[0]))  >= prod(s, sub(P.xs[1], P.xs[0])) >= UpperSum(f, P_First, a, P.xs[1]);
            assert prod(M, sub(b, P.xs[1])) >= prod(sup_rest, sub(b,P.xs[1])) >= UpperSum(f, P_next, P.xs[1], b);
            assert prod(M, sub(P.xs[1], P.xs[0])) + prod(M, sub(b, P.xs[1])) == prod(M, sub(b,a))  by {
                ProdDistributesOverSum(M, sub(P.xs[1], P.xs[0]), sub(b, P.xs[1]));
                assert sub(b,a) == sub(P.xs[1], P.xs[0]) + sub(b, P.xs[1]);
            }
            assert prod(s, sub(P.xs[1], P.xs[0])) + prod(sup_rest, sub(b, P.xs[1])) <= prod(M, sub(b,a));
        }

        assert u <= prod(M, sub(b,a));
    }

    lemma Prop_zero_one_six_lower_upper(f: real -> real, P: Partition, a: real, b: real)
        requires a < b
        requires isBounded(f, a, b)
        requires PartitionOf(a,b, P)
        ensures LowerSum(f, P, a, b) <= UpperSum(f, P, a, b)
        decreases |P.xs|
    {
        var l := LowerSum(f, P, a, b);
        var u := UpperSum(f, P, a, b);
        if |P.xs| == 2 {
            SupWidthGTEInfWidth(f, P.xs[0], P.xs[1], funcRange(f, P.xs[0], P.xs[1]));
        }else{
            var P_First := Partition(P.xs[..2], {P.xs[0], P.xs[1]});
            var P_next := Partition(P.xs[1..], P.s - {P.xs[0]});
            SupWidthGTEInfWidth(f, P.xs[0], P.xs[1], funcRange(f, P.xs[0], P.xs[1]));
            functionBoundedInMiddle(f, a, b, P.xs[1]);
            Prop_zero_one_six_lower_upper(f, P_next, P.xs[1], b);

        }
        assert l <= u;
    }

    ghost predicate SumDiffLessThanEpsilon(f: real -> real, P: Partition, a: real, b: real, epsilon: real)
        requires epsilon > 0.0
        requires a < b
        requires isBounded(f, a, b)
    {
        PartitionOf(a,b, P) && sub(UpperSum(f, P, a, b), LowerSum(f, P, a, b)) < epsilon
    }

    predicate positive(x: real)
    {
        x > 0.0
    }

    predicate IsRefinement(P1: Partition, P2: Partition)
    {
        forall x :: x in P1.s ==> x in P2.s
    }

    predicate CommonRefinement(P1: Partition, P2: Partition, P: Partition)
    {
        IsRefinement(P1, P) && IsRefinement(P2, P)
    }

    lemma Lemma_zero_two_two_i(f: real -> real, a: real, b: real, P: Partition, P2: Partition)
        requires a < b
        requires isBounded(f, a, b)
        requires PartitionOf(a,b, P)
        requires PartitionOf(a,b, P2)
        requires IsRefinement(P, P2)
        ensures LowerSum(f, P, a, b) <= LowerSum(f, P2, a, b) <= UpperSum(f, P2, a, b) <= UpperSum(f, P, a, b)

    lemma Lemma_zero_two_two_ii(f: real -> real, a: real, b: real, P1: Partition, P2: Partition)
        requires a < b
        requires isBounded(f, a, b)
        requires PartitionOf(a,b, P1)
        requires PartitionOf(a,b, P2)
        ensures LowerSum(f, P1, a, b) <= UpperSum(f, P2, a, b)

    lemma Corollary_zero_two_three(f: real -> real, a: real, b: real)
        requires a < b
        requires isBounded(f, a, b)
        ensures LowerIntegral(f, a, b) <= UpperIntegral(f, a, b)
    
    lemma valApproachingZero(a: real, b: real)
        requires forall epsilon :: positive(epsilon) ==> a <= b + epsilon
        ensures a <= b
    {
        if a > b {
            var diff := a - b;
            assert diff > 0.0;
            assert positive(diff/2.0);
            assert a <= b + diff/2.0;
            assert false;
        }

    }

    lemma Theorem_zero_two_four_forward(f: real -> real, a: real, b: real)
        requires a < b
        requires isBounded(f, a, b)
        requires forall epsilon :: positive(epsilon) ==> exists P :: SumDiffLessThanEpsilon(f, P,  a, b, epsilon)
        ensures RiemannIntegrable(f, a, b)
    {
        var M :| M > 0.0 && isBoundedBetween(f, a, b, M);
        var allPartitions := iset P | PartitionOf(a,b, P);
        var allPartitionSumsUpper := iset P | P in allPartitions :: UpperSum(f, P, a, b);
        var allPartitionSumsLower := iset P | P in allPartitions :: LowerSum(f, P, a, b);
        var canonical_P := Partition([a, b], {a, b});
        forall epsilon | positive(epsilon)
            ensures UpperIntegral(f, a, b) <= LowerIntegral(f, a, b) + epsilon
        {
                assert positive(epsilon);
                var P :| SumDiffLessThanEpsilon(f, P, a, b, epsilon);
                assert UpperSum(f, P, a, b) - LowerSum(f, P, a, b) < epsilon;
                assert P in allPartitions;
                assert UpperSum(f, P, a, b) in allPartitionSumsUpper;
                assert LowerSum(f, P, a, b) in allPartitionSumsLower;
                assert LowerSum(f, P, a, b) <= LowerIntegral(f, a, b);
                assert UpperIntegral(f, a, b) <= UpperSum(f, P, a, b);
                assert UpperSum(f, P, a, b) < LowerSum(f, P, a, b) + epsilon <= LowerIntegral(f, a, b) + epsilon;
        }
        valApproachingZero(UpperIntegral(f, a, b), LowerIntegral(f, a, b));
        Corollary_zero_two_three(f, a, b);
        assert RiemannIntegrable(f, a, b);
    }

    lemma {:vcs_split_on_every_assert } Problem3(f: real -> real, g: real -> real, a: real, b: real)
        requires a < b
        requires isBounded(f, a, b)
        requires isBounded(g, a, b)
        requires RiemannIntegrable(f, a, b)
        requires RiemannIntegrable(g, a, b)
        requires forall x :: a <= x <= b ==> f(x) <= g(x)
        ensures LowerIntegral(f, a, b) <= LowerIntegral(g, a, b)
    {
        var Mf :| Mf > 0.0 && isBoundedBetween(f,a,b,Mf);
        var Mg :| Mg > 0.0 && isBoundedBetween(g,a,b,Mg);
        var allPartitions := iset P | PartitionOf(a,b, P);

        var canonical_P := Partition([a, b], {a, b});
        var msf := funcRange(f, a, b);
        var msg := funcRange(g, a, b);
        assert f(a) in msf;
        assert g(a) in msg;
        BoundedAbove(f, a, b, a, b, Mf);
        BoundedAbove(g, a, b, a, b, Mg);
        BoundedBelow(f, a, b, a, b, Mf);
        BoundedBelow(g, a, b, a, b, Mg);
        assert upperBound(msf, Mf);
        assert lowerBound(msf, -Mf);
        var msf_sup := supremum(msf, f(a), Mf);
        var msf_inf := infimum(msf, f(a), -Mf);
        var msg_sup := supremum(msg, g(a), Mg);
        var msg_inf := infimum(msg, g(a), -Mg);
        // Prop_zero_one_six()
        // forall P | P in allPartitions
        //     ensures LowerSumAlt(f, P, a, b) <= LowerSumAlt(g, P, a, b)
            
        // {
        //     Prop_zero_one_six(f, P, a, b, msf_inf, msf_sup);
        //     Prop_zero_one_six(g, P, a, b, msg_inf, msg_sup);
        // }
        // assert forall P | P in allPartitions :: LowerSumAlt(f, P, a, b) <= LowerSumAlt(g, P, a, b);
        assert msf_sup <= msg_sup by {
            if msf_sup > msg_sup {
                var diff := msf_sup - msg_sup;
                assert diff > 0.0;
                assert positive(diff/2.0);
                assert msf_sup > msg_sup + diff/2.0;
                assert upperBound(msg, msg_sup + diff/2.0);
                assert !upperBound(msf, sub(msf_sup , diff/2.0));
                var z :| a <= z <= b && f(z) > sub(msf_sup, diff/2.0) && f(z) in msf;
                var gz := g(z);
                assert gz in msg;
                assert gz > msg_sup + diff/2.0;
                assert false;
            }
        }

    
        var x := UpperSum(f, canonical_P, a, b);
        var allPartitionLowerSumsF := iset P | P in allPartitions :: LowerSum(f, P, a, b);
        var allPartitionLowerSumsG := iset P | P in allPartitions :: LowerSum(g, P, a, b);

        var allPartitionUpperSumsF := iset P | P in allPartitions :: UpperSum(f, P, a, b);
        var allPartitionUpperSumsG := iset P | P in allPartitions :: UpperSum(g, P, a, b);
        // forall sum | sum in allPartitionUpperSumsF 
        //     ensures sum >= prod(-Mf, sub(b,a))
        //     ensures sum <= prod(Mf, sub(b,a))
        // {
        //     var P :| P in allPartitions && sum == UpperSumAlt(f, P, a, b);
        //     AllPartitionSetBoundedUpper(f, a, b, Mf, P);
        //     Prop_zero_one_six(f, P, a, b, msf_inf, msf_sup);
        //     SupLTEBound(f, P, a, b, Mf, msf_sup);
        //     prodLessThan(msf_sup, sub(b,a), Mf);
        //     assert UpperSumAlt(f, P, a, b) <= prod(msf_sup, sub(b,a)) <= prod(Mf, sub(b,a));

        // }
        forall sum | sum in allPartitionUpperSumsF 
            ensures prod(msf_inf, sub(b,a)) <= sum <= prod(msf_sup, sub(b,a))
        {
            var P :| P in allPartitions && sum == UpperSum(f, P, a, b);
            Prop_zero_one_six(f, P, a, b, msf_inf, msf_sup);
        }
        forall sum | sum in allPartitionUpperSumsG 
            ensures sum >= prod(msg_inf, sub(b,a))
            ensures sum <= prod(msg_sup, sub(b,a))
        {
            var P :| P in allPartitions && sum == UpperSum(g, P, a, b);
            Prop_zero_one_six(g, P, a, b, msg_inf, msg_sup);
        }

        forall sum | sum in allPartitionLowerSumsF 
            ensures prod(msf_inf, sub(b,a)) <= sum <= prod(msf_sup, sub(b,a))
        {
            var P :| P in allPartitions && sum == LowerSum(f, P, a, b);
            Prop_zero_one_six(f, P, a, b, msf_inf, msf_sup);
        }
        forall sum | sum in allPartitionLowerSumsG 
            ensures prod(msg_inf, sub(b,a)) <= sum <= prod(msg_sup, sub(b,a))
        {
            var P :| P in allPartitions && sum == LowerSum(g, P, a, b);
            Prop_zero_one_six(g, P, a, b, msg_inf, msg_sup);
        }
        var fsuminf := infimum(allPartitionLowerSumsF, LowerSum(f, canonical_P, a,b), prod(msf_inf, sub(b,a)));
        var fsumsup := supremum(allPartitionUpperSumsF, UpperSum(f, canonical_P, a,b), prod(msf_sup, sub(b,a)));
        var gsuminf := infimum(allPartitionLowerSumsG, LowerSum(g, canonical_P, a,b), prod(msg_inf, sub(b,a)));
        var gsumsup := supremum(allPartitionUpperSumsG, UpperSum(g, canonical_P, a,b), prod(msg_sup, sub(b,a)));
        assert LowerIntegral(f, a, b) <= LowerIntegral(g, a, b);
    }

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

