module libsort {
    import opened Std.Collections.Seq
    import opened Std.Relations

    predicate gte(x: int, y: int) {
        x >= y
    }

    predicate sortOnFirst(x: (int, char), y: (int, char)){
        x.0 >= y.0 || x.1 >= y.1
    }

    method testSortOnFirst()
    {
        assert sortOnFirst((1,'a'),(1,'a'));
        assert sortOnFirst((1,'a'),(1,'b'));
        assert sortOnFirst((2,'a'),(1,'a'));
        assert sortOnFirst((3,'b'),(1,'a'));
        assert !sortOnFirst((1,'a'),(3,'b'));
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

    lemma foox()
    ensures TotalOrdering(sortOnFirst)  
    {
    forall x, y | true
      ensures sortOnFirst(x, y) || sortOnFirst(y, x)
    {
        if sortOnFirst(x, y) {

        } else{
            assert !sortOnFirst(x,y);
            if x.0 > y.0 {
                assert x.1 < y.1;
            assert sortOnFirst(y,x);

            }else{

            }

        }

    }
    forall x, y | true
     ensures sortOnFirst(x, y) && sortOnFirst(y, x) ==> x == y;
     {
        assert x.0 == y.0;
     }
    }

    lemma SortedMapsEqual(xs: seq<(int, char)>)
        ensures multiset(Map(pairSelect, MergeSortBy(sortOnFirst,xs))) == multiset(Map(pairSelect, xs))
    {

    }
}