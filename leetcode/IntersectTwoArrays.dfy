include "../lib/seq.dfy"
module IntersectTwoArraysIO {
    import opened SeqCustom

    method toMultiset<A>(s: seq<A>) returns (mset: multiset<A>)
        ensures multiset(s) == mset
    {
        mset := multiset{};
        for i := 0 to |s| 
            invariant mset == multiset(s[0..i])
        {
            assert s == s[0..i] + [s[i]] + s[(i+1)..];
            mset := mset + multiset{s[i]};
        }
        assert s == s[0..|s|];
        return mset;
    }
     
    method msIntersection<A>(a: multiset<A>, b: multiset<A>) returns (c: multiset<A>)
        ensures c == a * b
    {
       c := multiset{};
       ghost var compared: multiset<A> := multiset{};
       var keys: multiset<A> := a; 
       while keys != multiset{}
           invariant keys !! compared
           invariant keys + compared == a
           invariant c == compared * b
       {
           var key :| key in keys;
           if key in b {
               c := c[key := if keys[key] < b[key] then keys[key] else b[key]];
           }
           keys := keys[key := 0];
           compared := compared[key := a[key]];
       }

    }

    method  IntersectTwoArrays(a: seq<int>, b: seq<int>) returns (c: seq<int>)
        ensures multiset(c) == multiset(a) * multiset(b)
    {
        var result: seq<int> := [];
        var ams := toMultiset(a);
        var bms := toMultiset(b);
        var cms := msIntersection(ams, bms);
        var compared: multiset<int> := multiset{};
        var keys: multiset<int> := cms;
        while keys != multiset{}
            invariant keys !! compared
            invariant keys + compared == cms
            invariant multiset(result) == compared
        {
            // assert exists key :: key in keys && keys[key] > 0;
            var key :| key in keys;
            // var oldResult := result;
            var oldms := multiset(result);
            // assert key !in oldResult;
            for i := 0 to cms[key]
                // invariant multiset(result) >= multiset(oldResult)
                invariant multiset(result)[key] == i
                invariant multiset(result) == oldms[key := i]
            {
                result := result + [key];
            }
            // assert multiset(result) == compared[key := cms[key]];
            keys := keys[key := 0];
            compared := compared[key := cms[key]];
        }
        return result;

    }

    //wrong
    method IntersectTwoArraysCopilot(a: seq<int>, b: seq<int>) returns (c: seq<int>)
        ensures forall i :: 0 <= i < |c| ==> c[i] in a && c[i] in b
        // ensures multiset(c) == multiset(a) * multiset(b)
    {
        var result := [];
        var j := 0;
        for i := 0 to |a|
            invariant j == |result|
            invariant forall k :: 0 <= k < j ==> result[k] in a && result[k] in b
        {
            if a[i] in b {
                result := result + [a[i]];
                j := j + 1;
            }
        }
        c := result;
    }

    method IntersectTwoArraysI(a: seq<int>, b: seq<int>) returns (c: seq<int>)
        ensures forall i :: 0 <= i < |c| ==> c[i] in a && c[i] in b
        ensures distinct(c)
    {
        var result := [];
        var j := 0;
        for i := 0 to |a|
            invariant j == |result|
            invariant forall k :: 0 <= k < j ==> result[k] in a && result[k] in b
            invariant distinct(result)
        {
            if a[i] in b && !(a[i] in result) {
                result := result + [a[i]];
                j := j + 1;
            }
        }
        c := result;
    }

    method setDiff<A>(a: set<A>, b: set<A>) returns (c: set<A>)
        ensures c == a - b
    {
        c := a;
        ghost var compared: set<A> := {};
        var b' := b;
        while b' != {}
            invariant b' !! compared
            invariant b' + compared == b
            invariant c == a - compared
        {
            var x :| x in b';
            c := c  - {x};
            compared := compared + {x};
            b' := b' - {x};
        }
    }

    method SetToSeq<T>(s: set<T>) returns (xs: seq<T>)
      ensures multiset(s) == multiset(xs)
    {
      xs := [];
      var left: set<T> := s;
      while left != {}
        invariant multiset(left) + multiset(xs) == multiset(s)
      {
        var x :| x in left;
        left := left - {x};
        xs := xs + [x];
      }
    }
    
    lemma SetToSeqContainsAll<T>(s: set<T>, xs: seq<T>)
        requires multiset(s) == multiset(xs)
        ensures forall x :: x in s ==> x in xs
    {
        forall x | x in s
            ensures x in xs
        {
            assert multiset(s) == multiset(xs);
            assert x in multiset(s);
        }
    }

    lemma SetToSeqContainsAllReverse<T>(s: set<T>, xs: seq<T>)
        requires multiset(s) == multiset(xs)
        ensures forall x :: x in xs ==> x in s
    {
        forall x | x in xs
            ensures x in s
        {
            assert multiset(s) == multiset(xs);
            assert x in multiset(xs);
        }
    }
    
    lemma SetToSeqDistinct<T>(s: set<T>, xs: seq<T>)
        requires multiset(s) == multiset(xs)
        ensures distinct(xs)
    {
        // assert forall x, y :: x in xs && y in xs && x != y ==> !(x in s) || !(y in s);
        assert forall x :: x in s ==> multiset(s)[x] == 1;
        forall x,y | x != y && 0 <= x <= y < |xs|
            ensures xs[x] != xs[y]
        {
            assert x != y;
            if xs[x] == xs[y] {
                assert xs == xs[0..x] + [xs[x]] + xs[(x+1)..y]+ [xs[y]] + xs[(y+1)..];
                assert multiset(s)[xs[x]] >= 2;
                assert false;
            }
        }
    }

    lemma SetNotEmpty<T>(s: set<T>, ms: multiset<T>, xs: seq<T>)
        requires multiset(s) == ms
        requires multiset(xs) == ms
        requires |s| == 1
        ensures s == {xs[0]}
    {
        assert s != {};
        if s != {xs[0]} {
            assert xs[0] in ms;
            assert xs[0] in s;
            var x :| x in s && x != xs[0];
            assert x in ms;
            assert false;
        }
    }

    lemma SetMsMinusX<T>(s: set<T>, ms: multiset<T>, x: T)
        requires x in ms
        requires x in s
        requires multiset(s) == ms
        ensures multiset(s - {x}) == ms[x := 0]
        ensures multiset(s - {x}) == ms - multiset{x}
    {
        assert x in s;
        assert x in ms;
        assert multiset(s - {x}) == ms[x := 0];
    }
    
    lemma SetMsMinus<T>(s: set<T>, ms: multiset<T>, xs: seq<T>)
        requires xs != []
        requires multiset(s) == ms
        requires multiset(xs) == ms
        ensures multiset(s - {xs[0]}) == multiset(xs[1..])
    {
        assert xs != [];
        assert xs == [xs[0]] + xs[1..];
        assert multiset(xs) == multiset([xs[0]]) + multiset(xs[1..]);
        if |xs| == 1 {
            assert xs[0] in ms;
            assert xs[0] in s;
            SetNotEmpty(s, ms, xs);
            assert multiset(s - {xs[0]}) == multiset({});
            assert multiset(xs[1..]) == multiset({});
        } else {
            assert xs[0] in ms;
            assert xs[0] in s;
            SetMsMinusX(s, ms, xs[0]);
            SetMsMinus(s - {xs[0]}, multiset(xs[1..]), xs[1..]);
        }
    }
    
    lemma SetToSeqToSet<T>(xs: seq<T>, s: set<T>)
        requires multiset(xs) == multiset(s)
        ensures ToSet(xs) == s
    {
        if |xs| == 0 {
            assert s == {};
        } else if |xs| == 1 {
            assert xs == [xs[0]];
            // assert |s| == 1;
            // assert s != {};
            // assert multiset(xs) == multiset({xs[0]});
            // assert xs[0] in s;
            assert xs[0] in multiset(xs);
            SetNotEmpty(s, multiset(xs), xs);
            // assert s == {xs[0]};
        }else{
            assert xs == [xs[0]] + xs[1..];
            // assert multiset(xs) == multiset([xs[0]]) + multiset(xs[1..]);
            SetMsMinus(s, multiset(xs), xs);
            SetToSeqToSet(xs[1..], s-{xs[0]});
        }
    }

    method findDifference(a: seq<int>, b: seq<int>) returns (c: seq<int>, d: seq<int>)
        ensures forall x :: x in c ==> x in a && !(x in b)
        ensures forall x :: x in d ==> x in b && !(x in a)
        ensures distinct(c)
        ensures distinct(d)
        ensures ToSet(c) == ToSet(a) - ToSet(b)
        ensures ToSet(d) == ToSet(b) - ToSet(a)
    {
        var aSet := ToSet(a);
        var bSet := ToSet(b);
        var cSet := setDiff(aSet, bSet);
        assert cSet == aSet - bSet;
        var dSet := setDiff(bSet, aSet);
        assert dSet == bSet - aSet;
        c := SetToSeq(cSet);
        SetToSeqToSet(c, cSet);
        assert forall x :: x in c ==> x in a && !(x in b) by {
            SetToSeqContainsAllReverse(cSet, c);
        }
        SetToSeqDistinct(cSet, c);
        d := SetToSeq(dSet);
        SetToSeqToSet(d, dSet);
        assert forall x :: x in d ==> x in b && !(x in a) by {
            SetToSeqContainsAllReverse(dSet, d);
        }
        SetToSeqDistinct(dSet, d);
    }
}