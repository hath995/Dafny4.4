
module GenericMergeSort {
    import opened Std.Collections.Seq
    trait Comparable<T(==)(!new)> {
        function Gt(x: T, y: T): bool

        predicate NotGte(x: T, y: T, Gt: (T,T) -> bool) {
            !Gt(x,y) && x != y
        }

        predicate NoMiddle(x: T, y: T, Gt: (T,T) -> bool) {
            !Gt(x,y) ==> Gt(y,x)
        }

        ghost predicate NoMiddleTotal(Gt: (T,T) -> bool) {
            forall x,y :: !Gt(x,y) ==> Gt(y,x)
        }

        ghost predicate TotalOrder(Gt: (T,T) -> bool) {
            forall a,b,c :: Gt(a,b) && Gt(b,c) ==> Gt(a,c)
        }
    }
    
    trait Sorted<T(==)(!new)> extends Comparable<T> {

        predicate SortedRec(list: seq<T>) {
            if list == [] then true else (forall y :: y in list[1..] ==> Gt(list[0], y) || list[0] == y) && SortedRec(list[1..])
        }

        function merge(xs: seq<T>, ys: seq<T>): seq<T>
            requires SortedRec(xs)
            requires SortedRec(ys)
            requires NoMiddleTotal(Gt)
            requires TotalOrder(Gt)
            ensures SortedRec(merge(xs, ys))
            ensures multiset(merge(xs,ys)) == multiset(xs)+multiset(ys)
        {

            if xs == [] then ys else
            if ys == [] then xs else
            if Gt(xs[0], ys[0]) then 
                assert xs == [xs[0]] + xs[1..];
                assert ys == [ys[0]] + ys[1..];
                assert forall x :: x in merge(xs[1..], ys) ==> x in xs[1..] || x in ys ==> (Gt(xs[0], x) || xs[0] == x);
                var result := [xs[0]] + merge(xs[1..], ys);
                assert forall x :: x in result[1..] ==> x in multiset(xs[1..])+multiset(ys);
                result
            else 
                assert Gt(ys[0], xs[0]);
                assert xs == [xs[0]] + xs[1..];
                assert ys == [ys[0]] + ys[1..];
                assert forall x :: x in merge(xs, ys[1..]) ==> x in xs || x in ys[1..] ==> (Gt(ys[0] , x) || ys[0] == x);
                var result := [ys[0]] + merge(xs, ys[1..]);
                assert forall x :: x in result[1..] ==> x in multiset(xs) + multiset(ys[1..]);
                result
        }

        function mergesort(xs: seq<T>): seq<T> 
            requires NoMiddleTotal(Gt)
            requires TotalOrder(Gt)
            ensures multiset(xs) == multiset(mergesort(xs))
            ensures SortedRec(mergesort(xs))
        {
            var n := |xs|;
            if n <= 1 then xs else
                assert xs == xs[0..n/2] + xs[n/2..];
                merge(mergesort(xs[0..n/2]), mergesort(xs[n/2..]))
        }
    }
    
    class MergeSort<T(==)(!new)> extends Sorted<T> {
        const CMP: (T,T) -> bool

        constructor(cmp: (T,T) -> bool)
        ensures CMP == cmp
        {
        CMP := cmp;
        }

        predicate Gt(x: T, y: T) {
            CMP(x,y)
        }
    }

    predicate gte(x: int, y: int) {
        x >= y
    }

    predicate sortOnFirst(x: (int, char), y: (int, char)){
        x.0 >= y.0
    }

    function pairSelect(t: (int, char)): int {
        t.0
    }

    function pairSecond(t: (int, char)): char {
        t.1
    }

    function joinPairs(t: (int, char)): multiset<char> 
        requires t.0 >= 0
    {
        var stub:=multiset{};
        stub[t.1:=t.0]
    }

    ghost predicate OrderFunctor<T(!new),U(!new)>(cmp: (T,T) -> bool, cmp2: (U,U) -> bool, mapFn: T -> U)
    {
        forall x: T, y: T :: cmp(x,y) ==> cmp2(mapFn(x), mapFn(y))
    }

    lemma OrderFunctorThings()
        ensures OrderFunctor(sortOnFirst, gte, pairSelect)
    {

    }

    lemma NoMiddleTuple(sorted: MergeSort<(int, char)>)
        requires sorted.CMP == sortOnFirst
        ensures sorted.NoMiddleTotal(sorted.Gt) 
    {
        forall x: (int,char),y: (int, char) 
            ensures !sorted.Gt(x,y) ==> sorted.Gt(y,x)
        {
           if !sorted.Gt(x,y) {
            assert !(x.0 >= y.0);
            assert x.0 < y.0;
            assert sortOnFirst(y,x);
           } 
        }
    }

    lemma NoMiddleInts(sorted: MergeSort<int>)
        requires sorted.CMP == gte
        ensures sorted.NoMiddleTotal(sorted.Gt) 
    {
        forall x: int,y: int 
            ensures !sorted.Gt(x,y) ==> sorted.Gt(y,x)
        {
           if !sorted.Gt(x,y) {
            assert !(x >= y);
            assert x < y;
            assert gte(y,x);
           } 
        }
    }

    lemma MsTotalOrder(sorted: MergeSort<(int, char)>)
        ensures forall x: (int,char),y: (int,char),z: (int,char) :: sorted.TotalOrder(sortOnFirst) 
    {}

    lemma MsTotalOrderInt(sorted: MergeSort<int>)
        ensures forall x: int,y: int, z: int :: sorted.TotalOrder(gte) 
    {}


    lemma sortedMapIsSorted(sorted: MergeSort<(int, char)>, xs: seq<(int, char)>, msorted: MergeSort<int>)
        requires sorted.CMP == sortOnFirst
        requires msorted.CMP == gte
        requires sorted.SortedRec(xs)
        ensures msorted.SortedRec(Map(pairSelect, xs))
    {
        // OrderFunctorThings();
        if xs == [] {

        }else{
            var mapped := Map(pairSelect, xs);
            forall y | y in mapped 
                ensures msorted.Gt(mapped[0], y) || mapped[0] == y
            {
                assert mapped[0] == pairSelect(xs[0]);
                var x :| x in xs && pairSelect(x) == y;
                assert x == xs[0] || x in xs[1..];
                assert sorted.Gt(xs[0], x) || x == xs[0];
                // assert sortOnFirst(xs[0], y) || mapped[0] == y;
            }
            sortedMapIsSorted(sorted, xs[1..], msorted);
            // MappedConcat(pairSelect, xs);
            reveal Map();
            assert mapped == [mapped[0]]+mapped[1..];
            assert msorted.SortedRec(mapped[1..]);
        }
    }
    lemma MapMultiset<T, R>(xs: seq<T>, fn: T->R, i: nat)
        requires i < |xs|
        ensures multiset(Map(fn, xs)) == multiset(Map(fn, xs[..i])) + multiset{fn(xs[i])}+multiset(Map(fn, xs[i+1..]))
    {
        reveal Map();
        assert xs == xs[..i] + [xs[i]] + xs[i+1..];
        assert Map(fn,xs) == Map(fn, xs[..i]) + [fn(xs[i])] + Map(fn, xs[i+1..]);
    }
    lemma MapMultisetConcat<T, R>(xs: seq<T>, ys: seq<T>, fn: T->R)
        ensures multiset(Map(fn, xs+ys)) == multiset(Map(fn, xs))+multiset(Map(fn, ys))
    {
        reveal Map();
        assert Map(fn, xs+ys) == Map(fn, xs) + Map(fn, ys);
    }

    lemma MapMultisetEqual<T, R>(xs: seq<T>, ys: seq<T>, fn: T->R)
        requires multiset(xs) == multiset(ys)
        ensures multiset(Map(fn, xs)) == multiset(Map(fn, ys))
    {
        reveal Map();
        if |xs| == 0 {

        }else{
            var x := xs[0];
            assert xs == [xs[0]]+xs[1..];
            assert x in multiset(xs);
            var y_index :| 0<= y_index < |ys| && ys[y_index] == x;
            assert ys == ys[..y_index] + [ys[y_index]] + ys[y_index+1..];
            assert x in ys;
            assert multiset(xs[1..]) == multiset(xs)-multiset{x};
            assert multiset(ys) == multiset(ys[..y_index])+multiset(ys[y_index+1..])+multiset{x};
            assert multiset(ys) == multiset(ys[..y_index]+ys[y_index+1..])+multiset{x};
            assert multiset(xs[1..]) == multiset(ys[..y_index])+multiset(ys[y_index+1..]);
            assert multiset(ys)-multiset{x} == multiset(ys[..y_index]+ys[y_index+1..]);
            MapMultisetEqual(xs[1..], ys[..y_index]+ ys[y_index+1..], fn);
            assert fn(x) == fn(ys[y_index]);
            MapMultiset(ys,fn, y_index);
            var mms := multiset(Map(fn,xs));
            var mmys := multiset(Map(fn,ys));
            assert mms == multiset(Map(fn,xs[1..])) + multiset{fn(x)};
            assert multiset(Map(fn, xs[1..])) == multiset(Map(fn, ys[..y_index]+ ys[y_index+1..]));
            MapMultisetConcat(ys[..y_index], ys[y_index+1..], fn);
            assert multiset(Map(fn, ys[..y_index]+ ys[y_index+1..])) == multiset(Map(fn,ys[..y_index])) +multiset(Map(fn,ys[y_index+1..]));
            assert mmys == multiset(Map(fn,ys[..y_index])) + multiset{fn(x)}+multiset(Map(fn,ys[y_index+1..]));
        }
    }

    lemma SortedMapsEqual(sorted: MergeSort<(int, char)>, xs: seq<(int, char)>)
        requires sorted.CMP == sortOnFirst
        requires sorted.NoMiddleTotal(sorted.Gt)
        requires sorted.TotalOrder(sorted.Gt)
        ensures multiset(Map(pairSelect, sorted.mergesort(xs))) == multiset(Map(pairSelect, xs))
    {
        var data := Map(pairSelect, sorted.mergesort(xs));
        var origdata := Map(pairSelect, xs);
        assert multiset(Map(pairSelect, sorted.mergesort(xs))) == multiset(Map(pairSelect, xs)) by {
            assert multiset(sorted.mergesort(xs)) == multiset(xs);
            MapMultisetEqual(sorted.mergesort(xs),xs, pairSelect);
        }
    }

    lemma SortedMapStillSorted(sorted: MergeSort<(int, char)>,  msorted: MergeSort<int>, xs: seq<(int, char)>)
        requires sorted.CMP == sortOnFirst
        requires msorted.CMP == gte
        requires sorted.SortedRec(xs)
        requires sorted.NoMiddleTotal(sorted.Gt)
        requires sorted.TotalOrder(sorted.Gt)
        ensures msorted.SortedRec(Map(pairSelect, xs))
    {
        OrderFunctorThings();
        if |xs| > 0 {
            var x:= xs[0];
            assert forall y :: y in xs[1..] ==> sorted.Gt(x,y) || x == y;
            var mapped := Map(pairSelect, xs);
            assert mapped == [mapped[0]]+mapped[1..];
            assert mapped[0] == pairSelect(x);
            assert forall ym :: ym in mapped[1..] ==> msorted.Gt(mapped[0],ym) || mapped[0] == ym by {
                forall ym | ym in mapped[1..]
                    ensures msorted.Gt(mapped[0], ym) || mapped[0] == ym
                {
                    var xy :| xy in xs[1..] && pairSelect(xy) == ym;

                }
            }
            SortedMapStillSorted(sorted, msorted, xs[1..]);
            assert mapped[1..] == Map(pairSelect, xs[1..]);
            assert msorted.SortedRec(mapped[1..]);
        }
    }

    lemma sortedEqualMsEqual(msorted: MergeSort<int>, xs: seq<int>, ys: seq<int>)
        requires multiset(xs) == multiset(ys)
        requires msorted.CMP == gte
        requires msorted.SortedRec(xs)
        requires msorted.SortedRec(ys)
        ensures xs == ys
    {
        if xs == [] {
            assert |multiset(xs)| == 0;
            assert ys == [];
        }else{
            assert |multiset(xs)| == |multiset(ys)|;
            assert |xs| == |ys|;
            assert ys[0] in multiset(ys);
            assert xs[0] in multiset(xs);
            assert xs[0] in ys;
            assert ys[0] in xs;
            assert xs[0] == ys[0] by {
                if ys[0] != xs[0] {
                    assert ys[0] in xs[1..];
                    assert xs[0] in ys[1..];
                    assert msorted.Gt(xs[0], ys[0]);
                    assert msorted.Gt(ys[0], xs[0]);
                    assert false;
                }
            }
            assert xs[0] == ys[0];
            assert xs == [xs[0]]+xs[1..];
            assert multiset(xs) == multiset{xs[0]}+multiset(xs[1..]);
            assert multiset(xs) - multiset{xs[0]}==multiset(xs[1..]);
            assert ys == [ys[0]]+ys[1..];
            assert multiset(ys) == multiset{ys[0]}+multiset(ys[1..]);
            assert multiset(xs[1..]) == multiset(ys[1..]);
            sortedEqualMsEqual(msorted, xs[1..], ys[1..]);
        }
    }

    lemma SortedMapEqualsSorted(sorted: MergeSort<(int, char)>,  msorted: MergeSort<int>, xs: seq<(int, char)>, ys: seq<int>)
        requires sorted.CMP == sortOnFirst
        requires msorted.CMP == gte
        requires Map(pairSelect, xs) == ys
        ensures Map(pairSelect, sorted.mergesort(xs)) == msorted.mergesort(ys)
    {
        reveal Map();
        MsTotalOrderInt(msorted);
        NoMiddleInts(msorted);
        assert msorted.SortedRec(msorted.mergesort(ys));
        if xs == [] {

        }else{
            assert multiset(ys) == multiset(Map(pairSelect, xs));
            var mapped := Map(pairSelect, sorted.mergesort(xs));
            var sortedints := msorted.mergesort(ys);
            SortedMapsEqual(sorted, xs);
            assert multiset(sortedints) == multiset(ys);
            assert multiset(mapped) == multiset(sortedints);
            SortedMapStillSorted(sorted, msorted, sorted.mergesort(xs));
            assert msorted.SortedRec(mapped);
            sortedEqualMsEqual(msorted, mapped, sortedints);
        }
    }

    lemma pairSecondStillEqual(sorted: MergeSort<(int, char)>, xs: seq<(int, char)>)
        requires sorted.CMP == sortOnFirst
        ensures multiset(Map(pairSecond, sorted.mergesort(xs))) == multiset(Map(pairSecond, xs))
    {
        assert multiset(sorted.mergesort(xs)) == multiset(xs);
        var mapped := Map(pairSecond, xs);
        var sMapped := Map(pairSecond, sorted.mergesort(xs));
        reveal Map();
        if xs == [] {
            assert multiset(Map(pairSecond, sorted.mergesort(xs))) == multiset(Map(pairSecond, xs));
        }else{
            MapMultisetEqual(xs, sorted.mergesort(xs), pairSecond);
            assert multiset(Map(pairSecond, sorted.mergesort(xs))) == multiset(Map(pairSecond, xs));
        }
    }

    method Main() {
        var a: seq<(int, char)> := [(2,'c'), (4,'a'), (1,'b')];
        var Sort := new MergeSort(sortOnFirst);
        NoMiddleTuple(Sort);
        print Sort.mergesort(a);
    }
}