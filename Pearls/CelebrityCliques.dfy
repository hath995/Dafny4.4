include "../examples/combinatorics.dfy"
include "../lib/seq.dfy"
include "./SeqFunctions.dfy"

module CelebrityCliques {
    import opened Combinatorics
    import opened SeqCustom
    import opened SeqFunctions
    // import opened Std.Collections.Seq



    predicate Knows<Person>(a: Person, b: Person)

    predicate IsCelebrityClique<Person>(cs: set<Person>, ps: set<Person>)
    {
        cs <= ps && forall x :: x in ps ==> (forall y :: y in cs ==> Knows(x, y) && (Knows(y, x) ==> x in cs))
    }

    lemma CelebrityCliqueIsUnique<Person>(ps: set<Person>, cs: set<Person>, cs': set<Person>)
        requires IsCelebrityClique(cs, ps)
        requires IsCelebrityClique(cs', ps)
        requires cs != {} && cs' != {}
        requires cs != cs'
        ensures false
    {
        // var c1 :| c1 in cs;
        // var c2 :| c2 in cs';
        // assert cs == cs' by {
        //     forall c1 | c1 in cs
        //         ensures c1 in cs'
        //     {
        //         var c2 :| c2 in cs';
        //         // assert c2 in ps;
        //         // assert c1 in ps;
        //         // assert Knows(c1, c2);
        //         // assert Knows(c2, c1);
        //         // assert c1 in cs';
        //     }

        //     forall c2 | c2 in cs'
        //         ensures c2 in cs
        //     {
        //         var c1 :| c1 in cs;
        //         // assert c2 in ps;
        //         // assert c1 in ps;
        //     }
        // }
    }

    function prepend<T(==)>(x: T, xs: seq<T>): seq<T> {
        [x]+ xs
    }

    function subsetSeqs<T(==)>(xs: seq<T>): seq<seq<T>>
        requires distinct(xs)
    {
        if xs == [] then
            [[]]
        else
            Map((ss: seq<T>) => prepend(xs[0], ss), subsetSeqs(xs[1..]))
            +
            subsetSeqs(xs[1..])
    }

    function seqSeqsToSet<T(==)>(xs: seq<T>): set<set<T>>
        requires distinct(xs)
    {
        set yy | yy in subsetSeqs(xs) :: ToSet(yy)
    }

    lemma subsetSeqsPowerset<T(==)>(xs: seq<T>)
        requires distinct(xs)
        ensures forall ss :: ss in PowerSet(ToSet(xs)) ==> ss in seqSeqsToSet(xs)
    {
        if xs == [] {
            assert ToSet(xs) == {};
            PowerSetEmptySet<T>({});
            assert PowerSet(ToSet(xs)) == {{}};

            assert forall ss :: ss in PowerSet(ToSet(xs)) ==> ss in seqSeqsToSet(xs);
        } else if |xs| == 1 {
            var x := xs[0];
            assert ToSet(xs) == {xs[0]};
            assert |Map((ss: seq<T>) => [xs[0]]+ss, [[]])| == 1;
            var f := (ss: seq<T>) => prepend(xs[0], ss);
            assert Map(f, [[]])[0] == f([]);
            assert f([]) == [x];
            calc {
                subsetSeqs(xs);
                Map(f, subsetSeqs(xs[1..]))+subsetSeqs(xs[1..]);
                Map(f, subsetSeqs(xs[1..]))+[[]];
                Map(f, [[]])+[[]];
                [[xs[0]]]+[[]];
                [[x],[]];
            }
            assert ToSet([x]) == {x};
            assert {} in seqSeqsToSet(xs);
            assert {x} in seqSeqsToSet(xs);
            PowerSetOneElem(ToSet(xs), x);
            assert PowerSet(ToSet(xs)) == {{},{x}};
            // assert [x] in subsetSeq(xs);
            assert forall ss :: ss in PowerSet(ToSet(xs)) ==> ss in seqSeqsToSet(xs);
        }else {
            subsetSeqsPowerset(xs[1..]);
            var x := xs[0];
            var f := (ss: seq<T>) => prepend(xs[0], ss);
            calc {
                subsetSeqs(xs);
                Map(f, subsetSeqs(xs[1..]))+subsetSeqs(xs[1..]);
            }
            assert xs == [x] + xs[1..];
            // var withX := set ss | ss in PowerSet(ToSet(xs[1..])) :: ss+{x};
            var mapped := Map(f, subsetSeqs(xs[1..]));
            // assert forall xx :: xx in mapped ==> ToSet(xx) in PowerSet(ToSet(xs));
            // assert forall wx :: wx in withX ==> wx in set ws | ws in Map(f, subsetSeqs(xs[1..])) :: ToSet(ws);
            // assert forall ss :: ss in PowerSet(ToSet(xs[1..])) ==> ss in seqSeqsToSet(xs[1..]);
            assert forall ss :: ss in PowerSet(ToSet(xs)) ==> ss in seqSeqsToSet(xs) by {
                forall ss | ss in PowerSet(ToSet(xs))
                    ensures ss in seqSeqsToSet(xs)
                {
                    if x in ss {
                        assert ss-{x} in PowerSet(ToSet(xs[1..]));
                        assert ss-{x} in seqSeqsToSet(xs[1..]);
                        var yy :| yy in subsetSeqs(xs[1..]) && ToSet(yy) == ss-{x};
                        assert f(yy) in mapped;
                        assert ToSet(f(yy)) == ss;
                        // assert f(ss)

                    }else {
                        assert ss in PowerSet(ToSet(xs[1..]));
                    }
                }
            }

        }
    }

    function FindCCliqueNaive<Person(==)>(xs: seq<Person>): seq<seq<Person>>
        requires distinct(xs)
    {
        var people := ToSet(xs);
        Filter((ss) => IsCelebrityClique(ToSet(ss),  people),subsetSeqs(xs))
    }

    predicate nonmember<Person(==)>(p: Person, cs: set<Person>) 
    {
        forall c :: c in cs ==> Knows(p, c) && !Knows(c, p)
    }

    lemma mapTest<T,R>(xs: seq<T>, f: T -> R)
        requires |xs| != 0
        ensures Map(f, xs)[0] == f(xs[0])
    {

 
        // assert |xs| != 0;
        // assert |xs| > 0;
        // assert |xs| == |Map(f, xs)|;
        // assert xs == [xs[0]]+xs[1..];
        // var res := Map(f, xs);
        // assert 0 < |xs|;
        // assert Map(f, [])  == []; 
        // assert forall i :: 0 <= i < |xs| ==> res[i] == f(xs[i]);
        // LemmaMapDistributesOverConcat(f, [xs[0]], xs[1..]);
        // assert Map(f, [xs[0]]) == [f(xs[0])]+Map(f,[xs[0]][1..]);
        // assert Map(f, [xs[0]]) == [f(xs[0])]+Map(f,[xs[0]][1..]);
        // assert res == [f(xs[0])]+Map(f, xs[1..]);
        // assert res[0] == f(xs[0]);
    }

    // lemma BirdTransorm<Person>(ps: seq<Person>)
    //     ensures filter(IsCelebrityClique, subsetSeqs(ps)) ==  filter(nonmember(p), filter(IsCelebrityClique) subsetSeqs)
    // {

    // }

}