include "../examples/combinatorics.dfy"
include "../lib/seq.dfy"
include "./SeqFunctions.dfy"

abstract module CelebrityCliques {
    import opened Combinatorics
    import opened SeqCustom
    import opened SeqFunctions
    // import opened Std.Collections.Seq
    type Person(!new, ==)



    predicate Knows(a: Person, b: Person)

    predicate IsCelebrityClique(cs: set<Person>, ps: set<Person>)
    {
        cs != {}
        && cs <= ps
        && forall x :: x in ps ==> (
            forall y :: y in cs ==> Knows(x, y) && (Knows(y, x) ==> x in cs)
        )
    }

    lemma CelebrityCliqueIsUnique(ps: set<Person>, cs: set<Person>, cs': set<Person>)
        requires IsCelebrityClique(cs, ps)
        requires IsCelebrityClique(cs', ps)
        // requires cs != {} && cs' != {}
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

    lemma lemmaSubsetSeqsContainsEmpty<T>(xs: seq<T>)
        requires distinct(xs)
        ensures [] in subsetSeqs(xs)
    {
    }

    lemma subsetSeqsContains<T>(xs: seq<T>)
        requires distinct(xs)
        ensures forall yy :: yy in subsetSeqs(xs) ==> forall y :: y in yy ==> y in xs
    {
        if xs == [] {
            assert forall yy :: yy in subsetSeqs(xs) ==> forall y :: y in yy ==> y in xs;
        }else if |xs|==1 {
            assert forall yy :: yy in subsetSeqs(xs) ==> forall y :: y in yy ==> y in xs;
        }else{
            var x := xs[0];
            assert xs == [xs[0]] + xs[1..];
            subsetSeqsContains(xs[1..]);
            var mapped := Map((ss: seq<T>) => prepend(xs[0], ss), subsetSeqs(xs[1..]));
            forall mm | mm in mapped
                ensures forall y :: y in mm ==> y in xs
            {
                forall y | y in mm
                    ensures y in xs
                {
                    if y == x {
                        assert x in xs;

                    }else{
                        var i :| 0 <= i < |mapped| && mapped[i] == mm;
                        assert mapped[i] == [x]+subsetSeqs(xs[1..])[i];
                        assert y in subsetSeqs(xs[1..])[i]; 
                        assert subsetSeqs(xs[1..])[i] in subsetSeqs(xs[1..]);
                        assert y in xs[1..];
                        assert y in xs;

                    }
                }
            }
            assert forall yy :: yy in subsetSeqs(xs) ==> forall y :: y in yy ==> y in xs;
        }
    }

    function seqSeqsToSet<T(==)>(xs: seq<T>): set<set<T>>
        requires distinct(xs)
    {
        set yy | yy in subsetSeqs(xs) :: ToSet(yy)
    }

    lemma subsetSeqsPowerset<T>(xs: seq<T>)
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

    lemma concatDifferent<T>(xs: seq<T>, ys: seq<T>, x: T)
        requires xs != ys
        ensures [x]+xs != [x]+ys
    {
        if |xs| != |ys| {

        }else{
            var i :| 0 <= i < |xs| && xs[i] != ys[i];
            assert ([x]+xs)[i+1] != ([x]+ys)[i+1];
        }
    }

    lemma subsetSeqsDistinct<T>(xs: seq<T>)
        requires distinct(xs)
        ensures distinct(subsetSeqs(xs))
    {
        if xs == [] {

        }else if |xs| == 1 {

        }else{
            var x := xs[0];
            assert xs == [x] + xs[1..];
            subsetSeqsDistinct(xs[1..]);
            var mapped := Map((ss: seq<T>) => prepend(xs[0], ss), subsetSeqs(xs[1..]));
            assert distinct(mapped) by {
                forall i,k | i != k && 0 <= i <= k < |mapped|
                    ensures mapped[i] != mapped[k]
                {
                    assert mapped[i] == prepend(xs[0], subsetSeqs(xs[1..])[i]);
                    assert mapped[k] == prepend(xs[0], subsetSeqs(xs[1..])[k]);
                    assert subsetSeqs(xs[1..])[i] != subsetSeqs(xs[1..])[k];
                    assert mapped[i] == [x]+subsetSeqs(xs[1..])[i];
                    assert mapped[k] == [x]+subsetSeqs(xs[1..])[k];
                    concatDifferent(subsetSeqs(xs[1..])[i], subsetSeqs(xs[1..])[k], x);
                    assert mapped[i] != mapped[k];
                }
                
            }
            forall xx | xx in mapped
                ensures xx !in subsetSeqs(xs[1..])
            {
                assert x in xx;
                subsetSeqsContains(xs[1..]);
                assert forall yy :: yy in subsetSeqs(xs[1..]) ==> x !in yy;
            }
            distincts(mapped, subsetSeqs(xs[1..]));

        }
    }

    lemma LemmaSubsetSeqsDistinct<T>(xs: seq<T>)
        requires distinct(xs)
        ensures forall ss :: ss in subsetSeqs(xs) ==> distinct(ss)
    {
        if xs == [] {
            // Base case: xs is empty, subsetSeqs([]) = [[]]
            // The empty sequence [] is trivially distinct
            assert forall ss :: ss in subsetSeqs(xs) ==> distinct(ss);
        } else if |xs| == 1 {
            // Base case: xs has one element, subsetSeqs([x]) = [[x], []]
            // Both [x] and [] are distinct sequences
            assert forall ss :: ss in subsetSeqs(xs) ==> distinct(ss);
        } else {
            // Inductive case: xs has more than one element
            var x := xs[0];
            assert xs == [x] + xs[1..];
            assert x !in xs[1..];
            
            // Recursively apply the lemma to xs[1..]
            LemmaSubsetSeqsDistinct(xs[1..]);
            subsetSeqsContains(xs[1..]);
            
            // subsetSeqs(xs) = Map(prepend(x, _), subsetSeqs(xs[1..])) + subsetSeqs(xs[1..])
            var mapped := Map((ss: seq<T>) => prepend(x, ss), subsetSeqs(xs[1..]));
            
            // All sequences in subsetSeqs(xs[1..]) are distinct by induction hypothesis
            assert forall ss :: ss in subsetSeqs(xs[1..]) ==> distinct(ss);
            
            // All sequences in mapped are distinct because:
            // 1. prepend(x, ss) adds x to the front of ss
            // 2. Since x is distinct from all elements in xs[1..] (because xs is distinct)
            // 3. And ss is distinct by induction hypothesis
            // 4. Therefore [x] + ss is distinct
            forall ss | ss in subsetSeqs(xs[1..])
                ensures distinct(prepend(x, ss))
            {
                assert distinct(ss); // by induction hypothesis
                assert x !in ss; // because x is distinct from all elements in xs[1..]
                assert distinct(prepend(x, ss)); // prepending a distinct element preserves distinctness
            }
            
            // All sequences in mapped are distinct
            assert forall ss :: ss in mapped ==> distinct(ss);
            
            // Therefore all sequences in subsetSeqs(xs) are distinct
            assert forall ss :: ss in subsetSeqs(xs) ==> distinct(ss);
        }
    }

    lemma setsNotEqualPlusOne<T>(ss: set<T>, yy: set<T>, x: T)
        requires ss != yy
        requires x !in ss
        requires x !in yy
        ensures {x}+ss != {x}+yy
    {}

    lemma subsetSeqToSetNotEqual<T>(xs: seq<T>)
        requires distinct(xs)
        ensures forall i,j :: i != j && 0 <= i < |subsetSeqs(xs)| && 0 <= j < |subsetSeqs(xs)| ==> ToSet(subsetSeqs(xs)[i]) != ToSet(subsetSeqs(xs)[j])
    {
        if |xs| <= 1 {

            assert forall i,j :: i != j && 0 <= i < |subsetSeqs(xs)| && 0 <= j < |subsetSeqs(xs)| ==> ToSet(subsetSeqs(xs)[i]) != ToSet(subsetSeqs(xs)[j]);
        }else{
            assert xs == [xs[0]]+xs[1..];
            subsetSeqsDistinct(xs);
            subsetSeqToSetNotEqual(xs[1..]);
            var rest := subsetSeqs(xs[1..]);
            var mapped := Map((ss: seq<T>) => prepend(xs[0], ss), subsetSeqs(xs[1..]));
            assert |mapped| == |rest|;
            assert subsetSeqs(xs) == mapped + rest;
            subsetSeqsContains(xs[1..]);
            forall i,j | i != j && 0 <= i < |subsetSeqs(xs)| && 0 <= j < |subsetSeqs(xs)|
                ensures ToSet(subsetSeqs(xs)[i]) != ToSet(subsetSeqs(xs)[j])
            {
                if i >= |rest| && j >= |rest| {

                    assert ToSet(subsetSeqs(xs)[i]) != ToSet(subsetSeqs(xs)[j]);
                }else if i < |rest| && j < |rest| {
                    subsetSeqsDistinct(xs[1..]);
                    forall m,n | m != n && 0 <= m < n < |mapped|
                        ensures ToSet(mapped[m]) != ToSet(mapped[n])
                    {
                        assert mapped[m] == [xs[0]]+subsetSeqs(xs[1..])[m];
                        assert mapped[n] == [xs[0]]+subsetSeqs(xs[1..])[n];
                        assert subsetSeqs(xs[1..])[m] != subsetSeqs(xs[1..])[n];
                        assert ToSet(subsetSeqs(xs[1..])[m]) != ToSet(subsetSeqs(xs[1..])[n]);
                        assert ToSet(mapped[m]) == {xs[0]}+ToSet(subsetSeqs(xs[1..])[m]);
                        assert ToSet(mapped[n]) == {xs[0]}+ToSet(subsetSeqs(xs[1..])[n]);
                        assert subsetSeqs(xs[1..])[m] in subsetSeqs(xs[1..]);
                        assert subsetSeqs(xs[1..])[n] in subsetSeqs(xs[1..]);
                        setsNotEqualPlusOne(ToSet(subsetSeqs(xs[1..])[m]), ToSet(subsetSeqs(xs[1..])[n]), xs[0]);
                    }

                    assert ToSet(subsetSeqs(xs)[i]) != ToSet(subsetSeqs(xs)[j]);
                }else{
                    var x := xs[0];
                    if i < |rest| {
                        assert j >= |rest|;
                        assert x in mapped[i];
                        assert subsetSeqs(xs)[j] in subsetSeqs(xs[1..]);
                        assert x !in subsetSeqs(xs)[j];
                    }else{
                        assert x in mapped[j];
                        assert subsetSeqs(xs)[i] in subsetSeqs(xs[1..]);
                        assert x !in subsetSeqs(xs)[i];
                        assert j < |rest| && i >= |rest|;
                    }
                    assert ToSet(subsetSeqs(xs)[i]) != ToSet(subsetSeqs(xs)[j]);
                }
            }

            assert forall i,j :: i != j && 0 <= i < |subsetSeqs(xs)| && 0 <= j < |subsetSeqs(xs)| ==> ToSet(subsetSeqs(xs)[i]) != ToSet(subsetSeqs(xs)[j]);
        }
    }

    /*
        filter (<|(p:ps) (subseqs (p:ps)))
    */

    function FindCCliqueNaive(xs: seq<Person>): seq<seq<Person>>
        requires distinct(xs)
        ensures forall cs :: cs in FindCCliqueNaive(xs) ==> IsCelebrityClique(ToSet(cs), ToSet(xs))
        ensures FindCCliqueNaive(xs) != [] ==> |FindCCliqueNaive(xs)| == 1
    {
        var people := ToSet(xs);
        var result := Filter((ss) => IsCelebrityClique(ToSet(ss),  people),subsetSeqs(xs));
        assert forall cs :: cs in result ==> IsCelebrityClique(ToSet(cs), ToSet(xs));
        // subsetSeqsDistinct(xs);
        subsetSeqToSetNotEqual(xs);
        assert |result| > 0 ==> |result| == 1 by {
            if |result| > 1 {
                FilterTargets((ss) => IsCelebrityClique(ToSet(ss),  people),subsetSeqs(xs));
                var cs := result[0];
                forall i | 1 < i < |result| 
                    ensures ToSet(result[i]) == ToSet(cs)
                {
                    if ToSet(result[i]) != ToSet(cs) {
                        CelebrityCliqueIsUnique(ToSet(cs), ToSet(result[i]), ToSet(xs));
                    }
                }
                assert false;
            }
        }
        result
    }

    predicate nonmember(p: Person, cs: set<Person>) 
    {
        forall c :: c in cs ==> Knows(p, c) && !Knows(c, p)
    }

    predicate member(p: Person, cs: set<Person>, ps: set<Person>) 
    {
        // forall x :: x in cs ==> Knows(x, p) && (Knows(p,x) <==> x in cs)
        forall x :: x in ps ==> Knows(x, p) && (Knows(p,x) <==> x in cs)
    }

    // lemma opps1(p: Person, cs: set<Person>, ps: set<Person>)
    //     requires p in ps
    //     requires cs <= ps
    //     requires nonmember(p, cs)
    //     ensures !member(p, cs, ps)
    // {
    // }

    // lemma opps4<Person(==)>(p: Person, cs: set, ps: set<Person>)
    //     requires p in ps
    //     requires cs <= ps
    //     requires !nonmember(p, cs)
    //     ensures member(p, cs, ps)
    // {
    // }

    // lemma opps2(p: Person, cs: set<Person>, ps: set<Person>)
    //     requires p in ps
    //     requires cs <= ps
    //     requires member(p, cs, ps)
    //     ensures !nonmember(p, cs)
    // {
    // }

    // lemma {:isolate_assertions} opps3<Person(==)>(p: Person, cs: set, ps: seq<Person>)
    //     requires |ps| > 1
    //     requires p == ps[0]
    //     requires cs <= ToSet(ps)
    //     requires forall q: Person :: q in ps ==> Knows(q,q)
    //     requires IsCelebrityClique(cs, ToSet(ps[1..]))
    //     requires !member(p, cs, ToSet(ps))
    //     ensures nonmember(p, cs)
    // {
    //     var x :| x in ps && (!Knows(x, p) || (Knows(x, p) && !(Knows(p,x) <==> x in cs)));
    //     if !Knows(x, p) {
    //         assert x != p;
    //         assert x in ps[1..];
    //         if !nonmember(p, cs) {
    //             var c :| c in cs && (!Knows(p, c) || Knows(c, p));
    //             if !Knows(p, c) {
    //                 assert false;
    //             }else if Knows(c, p) {

    //                 assert false;
    //             }
    //             assert false;
    //         }

    //         assert nonmember(p, cs);
    //     }else{

    //         if !nonmember(p, cs) {
    //             assert false;
    //         }
    //         assert nonmember(p, cs);
    //     }
    // }
    lemma opps5(p: Person, cs: set<Person>, ps: set<Person>)
        requires p in ps
        requires cs <= ps
        requires cs == {}
        requires !member(p, cs, ps)
        ensures nonmember(p, cs)
    {
        var x :| x in ps && (!Knows(x, p) || (Knows(x, p) && !(Knows(p,x) <==> x in cs)));
        if !Knows(x, p) {

            assert nonmember(p, cs);
        }else{

            assert nonmember(p, cs);
        }
    }

    // lemma NonMemberSimplification<Person(==)>(xs: seq, people: seq<Person>) 
    //     requires |xs| > 1
    //     requires ToSet(xs) <= ToSet(people)
    //     ensures IsCelebrityClique(ToSet(xs),  ToSet(people)) == IsCelebrityClique(ToSet(xs[1..]), ToSet(people)) && nonmember(xs[0], ToSet(xs[1..]))
    // {

    // }

    // lemma testMember(p: Person, ps: seq<Person>)
    //     requires p in ps
    //     requires forall x :: x in ToSet(ps) ==> Knows(x, p)
    //     ensures member(p, ToSet([]), ToSet(ps))
    // {}

    lemma testnonMember(p: Person, ps: seq<Person>)
        requires p in ps
        ensures nonmember(p, ToSet([]))
    {}

    /*
        ccliques [] = [[]]
        ccliques (p:ps) == map (p:) (filter (member p ps) css) ++
                           filter (nonmember p) css
                           where css = ccliques ps
    */
    function ccliques(ps: seq<Person>): seq<seq<Person>> 
        requires distinct(ps)
        ensures 1 <= |ccliques(ps)|
        ensures [] in ccliques(ps)
        ensures forall cs :: cs in ccliques(ps) ==> ToSet(cs) <= ToSet(ps)
        ensures forall cs :: cs in ccliques(ps) && |cs| > 0 ==> IsCelebrityClique(ToSet(cs), ToSet(ps))
    {
        if ps == [] then 
            [[]]
        else
            var p := ps[0];
            var css := ccliques(ps[1..]);
            var left := Map(pss => prepend(p, pss), Filter(cs => member(p, ToSet(cs), ToSet(ps)), css));
            var right := Filter(cs => nonmember(p, ToSet(cs)), css);
            assert [] in css;
            // testnonMember(p, ps);
            FilterHas(cs => nonmember(p, ToSet(cs)), css, []);
            assert [] in right;
            assert ps == [p]+ps[1..];
            ToSetConcat([p], ps[1..]);
            assert ToSet(ps[1..]) <= ToSet(ps);
            FilteredInXS(cs => nonmember(p, ToSet(cs)), css);
            var leftPre := Filter(cs => member(p, ToSet(cs), ToSet(ps)), css);
            FilteredInXS(cs => member(p, ToSet(cs), ToSet(ps)), css);
            forall cs | cs in left
                ensures ToSet(cs) <= ToSet(ps)
            {
                var i :| 0 <= i < |left| && left[i] == cs;
                var m :| 0 <= m < |leftPre| && prepend(p, leftPre[m]) == cs;
                ToSetConcat([p], leftPre[m]);
                assert ToSet(cs) == {p} + ToSet(leftPre[m]);
            }
            forall cs | cs in right
                ensures ToSet(cs) <= ToSet(ps)
            {
                
            }
            forall cs | cs in left+right && |cs| > 0
                ensures IsCelebrityClique(ToSet(cs), ToSet(ps))
            {}
            left + right
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

    // lemma BirdTransorm(ps: seq<Person>)
    //     ensures filter(IsCelebrityClique, subsetSeqs(ps)) ==  filter(nonmember(p), filter(IsCelebrityClique) subsetSeqs)
    // {

    // }

    function op(p: Person, cs: seq<Person>): seq<Person>
    {
        if cs == [] then 
            [p]
        else 
            var c := cs[0];
            if !Knows(p, c) then
                [p]
            else if !Knows(c, p) then
                cs
            else
                [p]+cs
    }
    // function opSetup<Person(!new)(==)>(ps: seq): (Person, seq<Person>) -> seq<Person> 
    //         ensures |opSetup(ps)(p,cs)| > 0 ==> IsCelebrityClique(ToSet(cclique'(cs)), ToSet(ps))
    // {
    //     (p: Person, cs: seq) =>
        
    //         if cs == [] then 
    //             [p]
    //         else 
    //             var c := cs[0];
    //             if !Knows(p, c) then
    //                 [p]
    //             else if !Knows(c, p) then
    //                 cs
    //             else
    //                 [p]+cs
        
    // }

    function cclique'(ps: seq<Person>): seq<Person>
        requires distinct(ps)
    {
        FoldRight(op, ps, [])
    }

    function cclique(ps: seq<Person>): seq<Person>
        requires distinct(ps)
    {
        ccliques(ps)[0]
    }

    lemma ccliqueNotNull(ps: seq<Person>)
        requires distinct(ps)
        requires |cclique(ps)| != 0
        ensures exists cs :: cs in subsetSeqs(ps) && IsCelebrityClique(ToSet(cs), ToSet(ps))

    {
        calc {
            cclique(ps);
            ccliques(ps)[0];
        }
        assert ccliques(ps)[0] in ccliques(ps);
        assert IsCelebrityClique(ToSet(ccliques(ps)[0]), ToSet(ps));
        assert ToSet(ccliques(ps)[0]) <= ToSet(ps);
        subsetSeqsPowerset(ps);
        assert ToSet(ccliques(ps)[0]) in PowerSet(ToSet(ps));
        var yy :| yy in  subsetSeqs(ps) && ToSet(yy) == ToSet(ccliques(ps)[0]);
        // assert ccliques(ps)[0] in subsetSeqs(ps);
    }

    lemma restIsAlsoCelebrityClique(ps: seq<Person>, cs: seq<Person>) 
        requires distinct(ps)
        requires forall q: Person :: q in ps ==> Knows(q,q)
        requires cs in subsetSeqs(ps)
        requires |cs| > 1
        requires cs[0] == ps[0]
        requires IsCelebrityClique(ToSet(cs), ToSet(ps))
        ensures IsCelebrityClique(ToSet(cs[1..]), ToSet(ps[1..]))
    {
        subsetSeqsContains(ps);
        subsetSeqsDistinct(ps);
        LemmaSubsetSeqsDistinct(ps);
        assert cs == [cs[0]]+cs[1..];
        assert cs[0] in ps;
        assert cs[0] !in ps[1..];

        assert ToSet(cs[1..]) != {};
        assert ToSet(cs[1..]) <= ToSet(ps[1..]);
        assert forall x :: x in ps[1..] ==> (
            forall y :: y in cs[1..] ==> Knows(x, y) && (Knows(y, x) ==> x in cs[1..])
        );

        assert forall x :: x in ToSet(ps[1..]) ==> (
            forall y :: y in ToSet(cs[1..]) ==> Knows(x, y) && (Knows(y, x) ==> x in ToSet(cs[1..]))
        );
        // assert forall q: Person :: q in ps[1..] ==> Knows(q,q);
        // assert forall p: Person, c: Person :: p in ps[1..] && c in cs[1..] ==> Knows(p,c);
        // assert forall p: Person, c: Person :: p in ps[1..] && c in cs[1..] ==> Knows(c,p) <==> p in ToSet(cs[1..]);
        assert IsCelebrityClique(ToSet(cs[1..]), ToSet(ps[1..]));
    }

    lemma {:isolate_assertions} cclique'Correctness(ps: seq<Person>)
        requires distinct(ps)
        requires forall q: Person :: q in ps ==> Knows(q,q)
        ensures ToSet(cclique'(ps)) <= ToSet(ps)
        ensures cclique'(ps) in subsetSeqs(ps)
        ensures (exists cs :: cs in subsetSeqs(ps) && IsCelebrityClique(ToSet(cs), ToSet(ps))) ==> IsCelebrityClique(ToSet(cclique'(ps)), ToSet(ps))
        // ensures |cclique'(ps)| > 0 ==> IsCelebrityClique(ToSet(cclique'(ps)), ToSet(ps))
        // ensures |cclique'(ps)| == 0 ==> (forall ss :: ss in subsetSeqs(ps) ==> !IsCelebrityClique(ToSet(cclique'(ss)), ToSet(ps)))
        // ensures |op(cs)| > 0 ==> IsCelebrityClique(ToSet(cclique'(cs)), ToSet(ps))
    {
        if ps == [] {

        } else if |ps| == 1 {
            assert ps[1..] == [];
            assert [] in subsetSeqs(ps[1..]);
            assert cclique'(ps) == [ps[0]];
            assert [] in subsetSeqs(ps[1..]);
            assert [ps[0]] == prepend(ps[0], []);
            assert [ps[0]] in subsetSeqs(ps);
            calc {
                cclique'(ps);
                FoldRight(op, ps, []);
                op(ps[0], FoldRight(op,[], []));
                op(ps[0], []);
                [ps[0]];
            }
            // assert ps[0] in ps;
            assert ToSet([ps[0]]) <= ToSet(ps);
            // assert IsCelebrityClique(ToSet([ps[0]]), ToSet(ps));
        } else{
            cclique'Correctness(ps[1..]);
            assert ps == [ps[0]]+ps[1..];
            var folded := cclique'(ps[1..]);
            calc {
                cclique'(ps);
                FoldRight(op, ps, []);
                op(ps[0], FoldRight(op, ps[1..], []));
                op(ps[0], cclique'(ps[1..]));
            }
            if folded == [] {
                calc{
                    op(ps[0], cclique'(ps[1..]));
                    op(ps[0], []);
                    [ps[0]];
                }
                // assert ps[0] in ps;
                assert ToSet([ps[0]]) <= ToSet(ps);
                // assert IsCelebrityClique(ToSet([ps[0]]), ToSet(ps));
                // assert |cclique'(ps)| == 0 ==> (forall ss :: ss in subsetSeqs(ps) ==> !IsCelebrityClique(ToSet(cclique'(ss)), ToSet(ps)));

            }else{
                assert |folded| >= 1;
                assert ToSet(folded) <= ToSet(ps[1..]);
                var p := ps[0];
                var c := folded[0];
                // assert ps[0] in ps;
                assert ToSet([ps[0]]) <= ToSet(ps);
                if exists cs :: cs in subsetSeqs(ps) && IsCelebrityClique(ToSet(cs), ToSet(ps)) {
                    if !Knows(p, c) {
                        LemmaSubsetSeqsDistinct(ps[1..]);
                        lemmaSubsetSeqsContainsEmpty(ps);
                        assert [ps[0]] == prepend(ps[0], []);
                        assert [ps[0]] in subsetSeqs(ps);
                        if !IsCelebrityClique(ToSet([p]), ToSet(ps)) {
                            if exists cs :: cs in subsetSeqs(ps[1..]) && IsCelebrityClique(ToSet(cs), ToSet(ps[1..])) {
                                assert !IsCelebrityClique(ToSet(folded), ToSet(ps));
                                assert false;
                            }else{
                                var cs :| cs in subsetSeqs(ps) && IsCelebrityClique(ToSet(cs), ToSet(ps)) && cs != [p];
                                var mapped := Map(ss => prepend(ps[0], ss), subsetSeqs(ps[1..]));
                                subsetSeqsContains(ps[1..]);
                                assert cs in mapped by {
                                    if cs !in mapped {
                                        assert cs in subsetSeqs(ps[1..]);
                                        assert false;
                                    }
                                }
                                assert ps[0] in cs;
                                assert !IsCelebrityClique(ToSet(cs), ToSet(ps)) by {
                                    var ss :| ss in subsetSeqs(ps[1..]) && cs == prepend(ps[0], ss);
                                    restIsAlsoCelebrityClique(cs, ps);
                                    // assert IsCelebrityClique(ToSet(ss), ToSet(ps[1..]));
                                    assert false;
                                }
                                assert false;

                            }
                            assert false;
                        }
                        assert IsCelebrityClique(ToSet([p]), ToSet(ps));
                    }else if !Knows(c, p) {
                        assert IsCelebrityClique(ToSet(folded), ToSet(ps));
                    }else{
                        if !IsCelebrityClique(ToSet([p]+folded), ToSet(ps)) {
                            if exists cs :: cs in subsetSeqs(ps[1..]) && IsCelebrityClique(ToSet(cs), ToSet(ps[1..])) {
                                assert IsCelebrityClique(ToSet(folded), ToSet(ps));
                                assert false;
                            }else{
                                var cs :| cs in subsetSeqs(ps) && IsCelebrityClique(ToSet(cs), ToSet(ps)) && cs != [p]+folded;
                                var mapped := Map(ss => prepend(ps[0], ss), subsetSeqs(ps[1..]));
                                subsetSeqsContains(ps[1..]);
                                assert cs in mapped by {
                                    if cs !in mapped {
                                        assert cs in subsetSeqs(ps[1..]);
                                        assert false;
                                    }
                                }
                                assert ps[0] in cs;
                                assert !IsCelebrityClique(ToSet(cs), ToSet(ps)) by {
                                    var ss :| ss in subsetSeqs(ps[1..]) && cs == prepend(ps[0], ss);
                                    restIsAlsoCelebrityClique(cs, ps);
                                    assert IsCelebrityClique(ToSet(ss), ToSet(ps[1..]));
                                    assert false;
                                }
                                assert false;

                            }
                            assert false;
                        }
                        assert IsCelebrityClique(ToSet([p]+folded), ToSet(ps));
                        assert [p]+folded == prepend(p, folded);
                        assert [p]+folded in subsetSeqs(ps);
                    }
                }else{
                    if !Knows(p, c) {
                        lemmaSubsetSeqsContainsEmpty(ps);
                        assert [ps[0]] == prepend(ps[0], []);
                        assert [ps[0]] in subsetSeqs(ps);
                    } else if !Knows(c, p) {
                    }else{
                        assert [p]+folded == prepend(p, folded);
                        assert [p]+folded in subsetSeqs(ps);

                    }
                }

            }

        }
    }


}

module celebs refines CelebrityCliques {
    datatype People = BradP | AngelinaJ | JohnnyD | Obama | Pleb1 | Pleb2 | Pleb3
    type Person = People
    const KnowsRel: set<(Person, Person)> := {
        (BradP, BradP),
        (AngelinaJ, AngelinaJ),
        (JohnnyD, JohnnyD),
        (Obama, Obama),
        (Pleb1, Pleb1),
        (Pleb2, Pleb2),
        (Pleb3, Pleb3),
        (BradP, AngelinaJ),
        (BradP, JohnnyD),
        (BradP, Obama),
        (AngelinaJ, JohnnyD),
        (AngelinaJ, Obama),
        (AngelinaJ, BradP),
        (JohnnyD, Obama),
        (JohnnyD, BradP),
        (JohnnyD, AngelinaJ),
        (Pleb1, BradP),
        (Pleb1, AngelinaJ),
        (Pleb1, JohnnyD),
        (Pleb1, Obama),
        (Pleb2, BradP),
        (Pleb2, AngelinaJ),
        (Pleb2, JohnnyD),
        (Pleb2, Obama),
        (Pleb3, BradP),
        (Pleb3, AngelinaJ),
        (Pleb3, JohnnyD),
        (Pleb3, Obama)
    }

    predicate Knows(a: Person, b: Person) {
        (a, b) in KnowsRel
    }

    lemma knowsReflexive() 
        ensures forall p: People :: true ==> Knows(p, p)
    {
        assert (BradP, BradP) in KnowsRel;
        assert (AngelinaJ, AngelinaJ) in KnowsRel;
        assert (JohnnyD, JohnnyD) in KnowsRel;
        assert (Obama, Obama) in KnowsRel;
        assert (Pleb1, Pleb1) in KnowsRel;
        assert (Pleb2, Pleb2) in KnowsRel;
        assert (Pleb3, Pleb3) in KnowsRel;
        assert Knows(BradP, BradP);
        assert Knows(AngelinaJ, AngelinaJ);
        assert Knows(JohnnyD, JohnnyD);
        assert Knows(Obama, Obama);
        assert Knows(Pleb1, Pleb1);
        assert Knows(Pleb2, Pleb2);
        assert Knows(Pleb3, Pleb3);
        if p: People :| p !in {BradP, AngelinaJ, JohnnyD, Obama, Pleb1, Pleb2, Pleb3} {
            assert (p,p) !in KnowsRel;
            assert p != BradP && p != AngelinaJ && p != JohnnyD && p != Obama && p != Pleb1 && p != Pleb2 && p != Pleb3;
            assert false;
        }
    }

    method {:test} Test() {
        knowsReflexive();
        var ps := [BradP, Pleb1,  AngelinaJ, Pleb2, Pleb3, JohnnyD];
        print "\nps: ";
        print ps;
        print "\n";
        assert distinct(ps);
        // print "\nsubsetSeqs(ps): ";
        // print subsetSeqs(ps);
        var cs := FindCCliqueNaive(ps);
        print "\ncs: ";
        print cs;
        print "\n";
        var css := ccliques(ps);
        print "\nccss: ";
        print css;
        print "\n";
        var ccss := cclique'(ps);
        print "\nccss: ";
        print ccss;
        print "\n";

    }
}