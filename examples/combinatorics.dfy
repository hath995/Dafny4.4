
module Combinatorics {

    function Factorial(n: int): int
        requires n >= 0
        ensures Factorial(n) == if n == 0 then 1 else n * Factorial(n - 1)
    {
        if n <= 0 then 1 else n * Factorial(n - 1)
    }

    function Numbers(): set<int> {
        {0,1,2,3,4,5,6,7,8,9}
    }

    function ToPairB<A(==),B(==)>(xs: set<A>, y: B): set<(A,B)> {
        set a | a in xs :: (a, y)
    }

    function ToPairA<A(==),B(==)>(x: A, bs: set<B>): set<(A,B)> {
        set b | b in bs :: (x, b)
    }

    function SevenTuples<A>(xs: set<A>): set<(A,A,A,A,A,A,A)> {
        set a1, a2, a3, a4, a5, a6, a7 | a1 in xs && a2 in xs && a3 in xs && a4 in xs && a5 in xs && a6 in xs && a7 in xs :: (a1, a2, a3, a4, a5, a6, a7)
    }

    function ThreeTuples<A>(xs: set<A>): set<(A,A,A)> {
        set a1, a2, a3 | a1 in xs && a2 in xs && a3 in xs :: (a1, a2, a3)
    }

    lemma ThreeTuplesSize<A>(xs: set<A>)
        ensures |ThreeTuples(xs)| == |xs| * |xs| * |xs|
    {
        CrossSize(xs, xs);
        CrossSize(xs, Cross(xs,xs));
        BijectionImpliesEqualCardinality(
                ThreeTuples(xs),
                Cross(xs, Cross(xs, xs)),
                (triple: (A, A, A)) => (triple.0, (triple.1, triple.2)),
                (pair: (A, (A, A))) => (pair.0, pair.1.0, pair.1.1)
            );
        // assert |ThreeTuples(xs)| == |xs| * |xs| * |xs|;
    }

    function Tuples<A>(xs: set<A>): set<(A,A)> {
        set a1, a2 | a1 in xs && a2 in xs :: (a1, a2)
    }

    lemma ToPairASize<A,B>(x: A, ys: set<B>)
        ensures |ToPairA(x, ys)| == |ys|
    {
        if |ys| == 0 {
            assert |ToPairA(x, ys)| == 0;
        } else {
            var b :| b in ys;
            assert forall b1 :: b1 in ys ==> ((x, b1) in ToPairA(x, ys));
            ToPairASize(x, ys - {b});
            assert ToPairA(x, ys) == {(x, b)} + ToPairA(x, ys - {b});
            assert |ToPairA(x, ys)| == |ys|;
        }
    }

    lemma ToPairSize<A,B>(xs: set<A>, y: B)
        ensures |ToPairB(xs, y)| == |xs|
    {
        if |xs| == 0 {
            assert |ToPairB(xs, y)| == 0;
        } else {
            var a :| a in xs;
            assert forall a1 :: a1 in xs ==> ((a1, y) in ToPairB(xs, y));
            ToPairSize(xs - {a}, y);
            assert ToPairB(xs, y) == {(a, y)} + ToPairB(xs - {a}, y);
            assert |ToPairB(xs, y)| == |xs|;
        }
    }

    function Cross<A,B>(a: set<A>, b: set<B>): set<(A,B)> {
        set a1, b1 | a1 in a && b1 in b :: (a1, b1)
    }

    lemma CrossTuplesEqual<A>(a: set<A>) 
        ensures Cross(a, a) == Tuples(a)
    {
        // if |a| == 0 {
        //     assert Cross(a, a) == {};
        // } else {
        //     var a1 :| a1 in a;
        //     CrossTuplesEqual(a - {a1});
        //     assert Cross(a, a) == Cross(a - {a1}, a) + ToPairB(a - {a1}, a1);
        //     assert Cross(a, a) == Tuples(a - {a1}) + ToPairB(a - {a1}, a1);
        // }
    }


    lemma CrossPlusOne<A,B>(a: set<A>, b: set<B>, x: B)
        requires x !in b
        ensures Cross(a, b + {x}) == Cross(a, b) + ToPairB(a, x)
        decreases |b|
    {
    }

    lemma CrossPlusOneA<A,B>(a: set<A>, b: set<B>, x: A)
        requires x !in a
        ensures Cross(a + {x}, b) == Cross(a, b) + ToPairA(x, b)
        decreases |a|
    {
    }

    lemma CrossSizePlusOneA<A,B>(a: set<A>, b: set<B>, x: A)
        // requires |b| > 0 
        requires x !in a
        ensures |Cross(a + {x}, b)| == |Cross(a, b)| + |b|
        decreases |a|
    {
        if |a| == 0 && |b| == 0 {
            assert |Cross(a + {x}, b)| == 0;
        } else if |a| == 0 {
            assert Cross(a + {x}, b) == ToPairA(x, b);
            ToPairASize(x, b);
        }else if |b| == 0 {
            assert |Cross(a, b)| == 0;
        } else {
            CrossPlusOneA(a, b, x);
            ToPairASize(x, b);
            assert |Cross(a + {x}, b)| == |Cross(a, b)| + |b|;
        }
    }
    
    
    lemma CrossSizePlusOne<A,B>(a: set<A>, b: set<B>, x: B)
        // requires |a| > 0 
        requires x !in b
        ensures |Cross(a, b + {x})| == |Cross(a, b)| + |a|
        decreases |b|
    {
        if |a| == 0 && |b| == 0 {
            assert |Cross(a, b + {x})| == 0;
        } else  if |a| == 0 {
            assert |Cross(a, b)| == 0;
        }else if |b| == 0 {
            assert Cross(a, b + {x}) == ToPairB(a, x);
            ToPairSize(a, x);
            assert |Cross(a, b + {x})| == |a|;
        } else {
            CrossPlusOne(a, b, x);
            ToPairSize(a, x);
            assert |Cross(a, b + {x})| == |Cross(a, b)| + |a|;
        }
    }

    lemma CrossSize<A, B>(a: set<A>, b: set<B>)
        ensures |Cross(a, b)| == |a| * |b|
        decreases |a| + |b|
    {
        if |a| == 0  {
            assert |Cross(a, b)| == 0;
        }else if |a| == 1 {
            var a1 :| a1 in a;
            CrossSizePlusOneA({}, b, a1);
            assert |a-{a1}| == 0;
            assert a == {} + {a1};
            assert Cross(a, b) == ToPairA(a1, b);
        } else {
            var a1 :| a1 in a;
            // var b1 :| b1 in b;
            CrossPlusOneA(a - {a1}, b, a1);
            // CrossPlusOne(a, b - {b1}, b1);
            CrossSizePlusOneA(a - {a1}, b, a1);
            // CrossSizePlusOne(a, b - {b1}, b1);
            CrossSize(a - {a1}, b);
            // CrossSize(a, b - {b1});
            calc {
                |Cross(a - {a1}, b)| + |b|;
                |a - {a1}| * |b| + |b|;
                (|a| - 1) * |b| + |b|;
                |a| * |b| - |b| + |b|;
                |a| * |b|;
            }
            // calc {
            //     |Cross(a, b - {b1})| + |a|;
            //     |a| * (|b| - 1) + |a|;
            //     |a| * |b| - |a| + |a|;
            //     |a| * |b|;
            // }
            assert Cross(a, b) == Cross(a - {a1}, b) + ToPairA(a1, b);
            ToPairASize(a1, b);
            // assert |Cross(a, b)| == |Cross(a - {a2}, b)| + |b|;
        }
    }
    datatype IteratedSet<A(==)> = Base(a: A) | Pair(left: A, right: IteratedSet<A>)

    // function CrossIteratedSet<A>(As: set<A>, s: IteratedSet<A>): IteratedSet<A> {

    // }

    lemma TripleSelectionEqualsCrossCross<T(==)>(s: set<T>)
        ensures (set a1, a2, a3 | a1 in s && a2 in s && a3 in s :: (a1, (a2, a3))) == Cross(s, Cross(s, s))
    {
    }

    lemma TripleSelectionEqualsCrossCross2<T(==)>(s: set<T>)
        ensures |(set a1, a2, a3 | a1 in s && a2 in s && a3 in s :: (a1, (a2, a3)))| == |Cross(s, Cross(s, s))|
    {
        TripleSelectionEqualsCrossCross(s);
    }

    lemma BijectionImpliesEqualCardinality<T(==), U(==)>(xs: set<T>, ys: set<U>, f: T -> U, g: U -> T)
        requires forall x :: x in xs ==> g(f(x)) == x
        requires forall y :: y in ys ==> f(g(y)) == y
        requires forall x :: x in xs ==> f(x) in ys
        requires forall y :: y in ys ==> g(y) in xs
        ensures |xs| == |ys|
    {
        if xs == {} {
            assert ys == {};
            assert |xs| == 0;
            assert |ys| == 0;
        }else if |xs| == 1 {
            var x :| x in xs;
            assert |xs-{x}| == 0;
            // assert f(x) in ys;
            // assert g(f(x)) == x;
            assert ys == {f(x)};
            //  by {
            //     // if y :| y in ys && f(x) != y {
            //     //     // assert g(y) in xs;
            //     //     assert false;
            //     // }
            // }
            assert |ys| == 1;
        } else {
            var x :| x in xs;
            BijectionImpliesEqualCardinality(xs - {x}, ys - {f(x)}, f, g);
            
            assert |xs| == |ys|;
        }
    }

    lemma TripleSelectionEqualsCrossCross3<T(==)>(s: set<T>)
        ensures |(ThreeTuples(s))| == |Cross(s, Cross(s, s))|
    {
        var target := set a1, a2, a3 | a1 in s && a2 in s && a3 in s :: (a1, a2, a3);
        // TripleSelectionEqualsCrossCross(s);
        // TripleSelectionEqualsCrossCross2(s);
        // forall p | p in Cross(s, Cross(s, s)) 
        //     ensures (p.0, p.1.0, p.1.1) in target
        // {
        //     assert (p.0, p.1.0, p.1.1) in target;
        // }

        // forall p | p in target 
        //     ensures (p.0, (p.1, p.2)) in Cross(s, Cross(s, s))
        // {
        //     assert (p.0, (p.1, p.2)) in Cross(s, Cross(s, s));
        // }
        BijectionImpliesEqualCardinality(
            Cross(s, Cross(s, s)),
            target,
            (pair: (T, (T, T))) => (pair.0, pair.1.0, pair.1.1),
            (triple: (T, T, T)) => (triple.0, (triple.1, triple.2))
        );
        assert |target| == |Cross(s, Cross(s, s))|;
    }


    lemma Test() {
        var twos := Cross(Numbers(), Numbers());
        CrossSize(Numbers(), Numbers());
        assert |twos| == 10 * 10;
        var threes := Cross(Numbers(), twos);
        var threes2 := set triple | triple in threes :: (triple.0, triple.1.0, triple.1.1);
        var threes3 := set a1, a2, a3 | a1 in Numbers() && a2 in Numbers() && a3 in Numbers() :: (a1, a2, a3);
        CrossSize(Numbers(), twos);
        assert |threes| == 10 * 10 * 10;
        // assert |threes2| == 10 * 10 * 10;
        // assert |threes2| == 10 * 10 * 10;
        // assert |threes3| == 10 * 10 * 10;
        // assert threes2 == threes3;
    }

    function PowerSet<A(==)>(elems: set<A>): set<set<A>> {
        set xs | xs <= elems
    }

    lemma PowerSetEmptySet<A(==)>(elems: set<A>)
        requires elems == {}
        ensures PowerSet(elems) == {{}}
    {
        assert elems <= elems;
        if xs :| xs in PowerSet(elems) && xs != {} {
            assert false;
        }
    }

    lemma PowerSetOneElem<A(==)>(elems: set<A>, x: A)
        requires |elems| == 1
        requires x in elems
        ensures PowerSet(elems) == {{}, {x}}
    {
            if xs :| xs in PowerSet(elems) && xs != {} && xs != {x} {
                assert |elems-{x}| == 0;
                assert false;
            }
            assert PowerSet(elems) == {{},{x}};
    }

    function NatPow(base: nat, exp: nat): nat {
        if exp == 0 then 
            1 
        else if exp == 1 then
            base
        else base * NatPow(base, exp-1)
    }

    lemma NatPowAdd(base: nat, x: nat, y: nat)
        ensures NatPow(base, x) * NatPow(base, y) == NatPow(base, x + y)
    {
        if x == 0 {

        } else if x == 1 {

        }else {
            NatPowAdd(base, x-1, y);
        }
    }

    lemma PowerSetSize<A(==)>(elems: set<A>)
        ensures |PowerSet(elems)| == NatPow(2, |elems|)
    {
        if |elems| == 0 {
            assert elems == {};
            assert {} in PowerSet(elems);
            if xs :| xs in PowerSet(elems) && xs != {} {
                assert false;
            }
            assert PowerSet(elems) == {{}};
            // assert NatPow(2, 0) == 1;
            // assert |PowerSet(elems)| == NatPow(2, |elems|);
        } else if |elems| == 1 {
            var x :| x in elems;
            // assert {} in PowerSet(elems);
            // assert {x} in PowerSet(elems);
            if xs :| xs in PowerSet(elems) && xs != {} && xs != {x} {
                assert |elems-{x}| == 0;
                assert false;
            }
            assert PowerSet(elems) == {{},{x}};
            // assert |PowerSet(elems)| == NatPow(2, |elems|);
        }else {
            var x :| x in elems;
            var subsets := PowerSet(elems);
            var subsetsMinusX := PowerSet(elems-{x});
            PowerSetSize(elems-{x});
            assert forall ss :: ss in subsetsMinusX ==> ss in subsets;
            assert |subsetsMinusX| == NatPow(2, |elems|-1);
            var withX := set ss | ss in subsetsMinusX :: ss+{x};
            BijectionImpliesEqualCardinality(subsetsMinusX, withX, (xs: set<A>) => xs+{x}, (xx: set<A>) => xx-{x});
            assert |withX| == |subsetsMinusX|;
            assert |withX| == NatPow(2, |elems|-1);
            assert forall xx :: xx in withX ==> xx in subsets;
            assert subsets == withX + subsetsMinusX by {
                forall xx | xx in subsets
                    ensures xx in withX || xx in subsetsMinusX
                {
                    if x in xx {
                        var wox := xx-{x};
                        assert wox in subsetsMinusX;
                        assert wox+{x} in withX;
                        assert xx == wox+{x};
                        assert xx in withX;
                    }else{
                        assert xx in subsetsMinusX;

                    }
                }
            }
            // assert |PowerSet(elems)| == NatPow(2, |elems|);

        }
    }

    // function telephoneNumbers(): set<seq<int>> {
    //     set x | |x| == 7 && forall i :: 0 <= i < |x| ==> (x[i] in Numbers()) 
    // }

    // function BinomialCoefficient(n: int, k: int): int
    //     requires n >= 0 && k >= 0 && k <= n
    //     ensures BinomialCoefficient(n, k) == Factorial(n) / (Factorial(k) * Factorial(n - k))
    // {
    //     if k == 0 || k == n then 1 else BinomialCoefficient(n - 1, k - 1) + BinomialCoefficient(n - 1, k)
    // }
}