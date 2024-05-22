
module InversionDefs {

    predicate Sorted(xs: seq<int>) {
        forall i, j | 0 <= i < j < |xs| :: xs[i] <= xs[j]
    }

    predicate IsInverted(xs: seq<int>, i: int, j: int) {
        0 <= i < j < |xs| && xs[i] > xs[j]
    }

    function inversionSet(xs: seq<int>): set<(int,int)> {
        set i,j | 0 <= i < j < |xs| && IsInverted(xs, i, j) :: (i,j)
    }

    function countInversion(xs: seq<int>): int {
        |inversionSet(xs)|
    }

    function inversersionSetJoined(xs: seq<int>, ys: seq<int>): set<(int,int)> 
    {
        var n := |xs| + |ys|;
        var xsys := xs + ys;
        assert |xsys| == n;
        set i, j | 0 <= i < |xs| && |xs| <= j < n && IsInverted(xsys, i, j) :: (i, j)
    }

    function JoinedWith(xs: seq<int>, ys: seq<int>, k: int): set<(int,int)> 
        requires 0 <= k < |xs|
    {
        set  j | |xs| <= j < |xs| + |ys| && IsInverted(xs + ys, k, j) :: (k, j)
    }

    ghost function JoinedWith2(xs: seq<int>, ys: seq<int>, k: int): set<(int,int)> 
        requires 0 <= k < |xs|
    {
        if ys == [] then
            {}
        else
            if IsInverted(xs + ys, k, |xs|) then
                {(k, |xs|)}+pairSetRmap(JoinedWith2(xs, ys[1..], k), 1)
            else
                pairSetRmap(JoinedWith2(xs, ys[1..], k),1)
    }

    lemma JoinedWith2Size(xs: seq<int>, ys: seq<int>, k: int)
        requires 0 <= k < |xs|
        ensures ys == [] ==> |JoinedWith2(xs, ys, k)| == 0
        ensures ys != [] && IsInverted(xs+ys, k, |xs|) ==> |JoinedWith2(xs, ys, k)| == 1+|pairSetRmap(JoinedWith2(xs, ys[1..], k), 1)|
        ensures ys != [] && !IsInverted(xs+ys, k, |xs|) ==> |JoinedWith2(xs, ys, k)| == |pairSetRmap(JoinedWith2(xs, ys[1..], k), 1)|
    {
        if ys == [] {
            assert JoinedWith2(xs, ys, k) == {};
            assert |JoinedWith2(xs, ys, k)| == 0;
        }else{
            if IsInverted(xs + ys, k, |xs|) {
                JoinedWithSame(xs, ys[1..], k);
                assert forall x :: x in JoinedWith2(xs, ys[1..], k) ==> rmap(x, 1).1 > |xs|;
                assert (k, |xs|) !in pairSetRmap(JoinedWith2(xs, ys[1..], k), 1) by {
                    if (k, |xs|) in pairSetRmap(JoinedWith2(xs, ys[1..], k), 1) {
                        pairSetRmapInverse(JoinedWith2(xs, ys[1..], k), 1, (k, |xs|));
                        assert rmap((k, |xs|), -1) == (k, |xs|);
                        assert false;
                    }
                }
                assert JoinedWith2(xs, ys, k) == {(k, |xs|)}+pairSetRmap(JoinedWith2(xs, ys[1..], k), 1);
                assert |JoinedWith2(xs, ys, k)| == 1+|pairSetRmap(JoinedWith2(xs, ys[1..], k), 1)|;
            }else{
                assert JoinedWith2(xs, ys, k) == pairSetRmap(JoinedWith2(xs, ys[1..], k),1);
                assert |JoinedWith2(xs, ys, k)| == |pairSetRmap(JoinedWith2(xs, ys[1..], k), 1)|;
            }
        }
    }

    function pmap(ps: (int, int), i: int): (int, int)
    {
        (ps.0 + i, ps.1 + i)
    }

    function rmap(ps: (int, int), i: int): (int, int)
    {
        (ps.0, ps.1 + i)
    }
    
    ghost function pairSetRmap(ss: set<(int, int)>, i: int): set<(int, int)> 
        ensures forall pair :: pair in ss ==> rmap(pair, i) in pairSetRmap(ss, i)
    {
        if ss == {} then
            assert |ss| == 0;
            {}
        else
            var pair :| pair in ss;
            {rmap(pair, i)} + pairSetRmap(ss-{pair}, i)
    }

    function pairKMap(ss: set<(int, int)>, k: int, i: int): set<(int, int)> 
        requires 0 <= k
        requires 0 < i
    {
        (set pair | pair in ss && pair.0 < k :: (pair.0, pair.1 + i)) +
        set pair | pair in ss && pair.0 >= k :: (pair.0 + i, pair.1 + i)
    }

    lemma {:vcs_split_on_every_assert} pairKMapSize(ss: set<(int, int)>, k: int, i: int) 
        requires 0 <= k
        requires 0 < i
        ensures |pairKMap(ss, k, i)| == |ss|
    {
        if ss == {} {
            assert |ss| == 0;
            assert |pairKMap(ss, k, i)| == 0;
        }else{
            var x :| x in ss;
            assert ss == (ss-{x})+{x};
            if x.0 < k {
                pairKMapSize(ss-{x}, k, i);
                assert (x.0, x.1+i) in pairKMap(ss,k,i);
                assert (x.0, x.1+i) !in pairKMap(ss-{x},k,i);
                assert pairKMap(ss, k, i) == {(x.0, x.1+i)} + pairKMap(ss-{x},k,i);
                assert |pairKMap(ss, k, i)| == 1 + |pairKMap(ss-{x},k,i)|;
                assert |pairKMap(ss, k, i)| == |ss|;
            }else{
                pairKMapSize(ss-{x}, k, i);
                assert pairKMap(ss, k, i) == {(x.0+i, x.1+i)} + pairKMap(ss-{x},k,i);
                assert |pairKMap(ss, k, i)| == |ss|;
            }

        }
    }

    function pairSetMap(ss: set<(int, int)>, i: int): set<(int, int)> 
    {
        set pair | pair in ss :: (pair.0 + i, pair.1 + i)
    }

    ghost function pairSetMap2(ss: set<(int, int)>, i: int): set<(int, int)> 
        ensures forall pair :: pair in ss ==> pmap(pair, i) in pairSetMap2(ss, i)
    {
        if ss == {} then
            assert |ss| == 0;
            {}
        else
            var pair :| pair in ss;
            {pmap(pair, i)} + pairSetMap2(ss-{pair}, i)
    }

    function inversionSetPartial(xs: seq<int>, i: int): set<(int, int)> {
        set k, j | 0 <= k < i <= |xs| && 0 <= j < |xs| && IsInverted(xs, k, j) :: (k, j)
    }

    function inversionSetRowPartial(xs: seq<int>, i: int, j: int): set<(int, int)> 
        // ensures forall x: (int, int) :: x in inversionSetRowPartial(xs, i, j) ==> x.0 == i
    {
        set k | 0 <= i < k < j <= |xs| && IsInverted(xs, i, k) :: (i, k)
    }

    lemma seqMsLength(xs: seq<int>, ys: seq<int>)
        requires multiset(xs) == multiset(ys)
        ensures |xs| == |ys|
    {
        if xs == [] {

        }else if |xs|==1 {
            assert xs[0] in multiset(xs);
            assert xs[0] == ys[0];
        }else{
            var x := xs[0];
            assert xs == [xs[0]]+xs[1..];
            assert x in multiset(xs);
            assert x in multiset(ys);
            var k :| 0<=k < |ys| && ys[k] == x;
            assert ys == ys[0..k]+[x]+ys[k+1..];
        }
    }

    // lemma forallPartial(xs: seq<int>, i: int, j: int) 
    //     requires 0 <= i < j < |xs|
    //     ensures forall pair :: pair in inversionSetRowPartial(xs, i, j) ==> IsInverted(xs, pair.0, pair.1)
    // {}

    // lemma partial(xs: seq<int>, i: int , j: int)
    //     requires 0 <= i < j < |xs|
    //     ensures IsInverted(xs, i, j) ==> inversionSetRowPartial(xs, i, j+1) == inversionSetRowPartial(xs, i, j) + {(i,j)}
    //     ensures !IsInverted(xs, i, j) ==> inversionSetRowPartial(xs, i, j+1) == inversionSetRowPartial(xs, i, j)
    // {
    //     // var test := set k | 0 <= i < k < j+1 <= |xs| && proper(xs, (i, k), j+1) && IsInverted(xs, i, k) :: (i, k);
    //     var most := inversionSetRowPartial(xs, i, j);
    //     var test := set k | 0 <= i < k < j+1 <= |xs|  && IsInverted(xs, i, k) :: (i, k);
    //     assert test == inversionSetRowPartial(xs, i, j+1);
    //     if IsInverted(xs, i, j) {
    //         assert (i, j) !in inversionSetRowPartial(xs, i, j);
    //         assert (i, j) !in most;
    //         assert i < j < j+1 <= |xs|;
    //         assert IsInverted(xs, i, j) && (i,j) in test;
    //         assert forall x :: x in most ==> x in test;
    //         assert most < test;
    //         assert most + {(i,j)} == test;
    //     }else{
    //         assert forall x :: x in most ==> x in test;
    //         assert most <= test;
    //         // assert inversionSetRowPartial(xs, i, j+1) == inversionSetRowPartial(xs, i, j);
    //     }
    // }

    // lemma inversionSetPartialLemma(xs: seq<int>, i: int)
    //     requires 0 <= i < |xs|
    //     ensures inversionSetPartial(xs, i+1) == inversionSetPartial(xs, i) + inversionSetRowPartial(xs, i, |xs|)
    // {
    //     forall x | x in inversionSetRowPartial(xs, i, |xs|)
    //         ensures x in inversionSetPartial(xs, i+1)
    //     {
    //         assert IsInverted(xs, x.0, x.1);
    //         assert x.0 == i;
    //         assert 0 <= x.0 < i+1 <= |xs|;
    //         assert x in inversionSetPartial(xs, i+1);
    //     }
    // }

    lemma pairSetMap2Inverse(ss: set<(int, int)>, i: int, pair: (int, int))
        requires pair in pairSetMap2(ss, i)
        ensures pmap(pair, -i) in ss
    {
    }

     lemma pairMapSize(xs: seq<int>, i: int)
        ensures |pairSetMap(inversionSet(xs), i)| == |inversionSet(xs)|
    {
        pairSetMapLemma(inversionSet(xs), i);
    }

    lemma pairSetMap2Lemma(ss: set<(int, int)>, i: int)
        ensures |pairSetMap2(ss, i)| == |ss|
    {
        if ss == {} {
            assert |ss| == 0;
            assert |pairSetMap2(ss, i)| == 0;
        }else{
            var result := pairSetMap2(ss, i);
            var pair :| pair in ss && {pmap(pair, i)} + pairSetMap2(ss-{pair}, i) == result;
            var mpair := pmap(pair, i);
            assert mpair in result;
            pairSetMap2Lemma(ss-{pair}, i);
            assert pair !in ss-{pair};

            assert mpair !in pairSetMap2(ss-{pair}, i) by {
                if mpair in pairSetMap2(ss-{pair}, i) {
                    assert mpair in pairSetMap2(ss-{pair}, i);
                    pairSetMap2Inverse(ss-{pair}, i, mpair);
                    assert pmap(mpair, -i) in ss-{pair};
                    assert pmap(mpair, -i) == pair;
                    assert false;
                }
            }
            assert result == {mpair} + pairSetMap2(ss-{pair}, i);
            assert |result| == 1 + |pairSetMap2(ss-{pair}, i)|;
        }

    }

    lemma pairsEqual(ss: set<(int, int)>, i: int)
        ensures pairSetMap(ss, i) == pairSetMap2(ss, i)
    {
    }

    lemma pairSetMapLemma(ss: set<(int, int)>, i: int)
        ensures |pairSetMap(ss, i)| == |ss|
    {
        pairSetMap2Lemma(ss, i);
        pairsEqual(ss, i);
        assert |pairSetMap(ss, i)| == |pairSetMap2(ss, i)|;
        assert |pairSetMap(ss, i)| == |ss|;
    }
    lemma pairSetMapInverse(ss: set<(int, int)>, i: int, pair: (int, int))
        requires pair in pairSetMap(ss, i)
        ensures pmap(pair, -i) in ss
    {
    }

    lemma pairSetRmapInverse(ss: set<(int, int)>, i: int, pair: (int, int))
        requires pair in pairSetRmap(ss, i)
        ensures rmap(pair, -i) in ss
    {
    }

    lemma pairSetRmapLemma(ss: set<(int, int)>, i: int)
        ensures |pairSetRmap(ss, i)| == |ss|
    {
        if ss == {} {
            assert |ss| == 0;
            assert |pairSetRmap(ss, i)| == 0;
        }else{
            var result := pairSetRmap(ss, i);
            var pair :| pair in ss && {rmap(pair, i)} + pairSetRmap(ss-{pair}, i) == result;
            var mpair := rmap(pair, i);
            assert mpair in result;
            pairSetRmapLemma(ss-{pair}, i);
            assert pair !in ss-{pair};

            assert mpair !in pairSetRmap(ss-{pair}, i) by {
                if mpair in pairSetRmap(ss-{pair}, i) {
                    assert mpair in pairSetRmap(ss-{pair}, i);
                    pairSetRmapInverse(ss-{pair}, i, mpair);
                    assert rmap(mpair, -i) in ss-{pair};
                    assert rmap(mpair, -i) == pair;
                    assert false;
                }
            }
            assert result == {mpair} + pairSetRmap(ss-{pair}, i);
            assert |result| == 1 + |pairSetRmap(ss-{pair}, i)|;
        }

    }


    lemma inversersionSetJoinedFirsts(xs: seq<int>, ys: seq<int>)
        requires xs != []
        ensures inversersionSetJoined(xs, ys) == JoinedWith(xs, ys, 0) + pairSetMap2(inversersionSetJoined(xs[1..], ys),1)
    {
        forall pair | pair in inversersionSetJoined(xs, ys) 
            ensures pair in JoinedWith(xs, ys, 0) + pairSetMap2(inversersionSetJoined(xs[1..], ys),1)
        {
            if pair.0 == 0 {
                assert pair in JoinedWith(xs, ys, 0);
            }else{
                assert pair !in JoinedWith(xs, ys, 0);
                assert pmap(pair, -1) in inversersionSetJoined(xs[1..], ys);
                assert pair in pairSetMap2(inversersionSetJoined(xs[1..], ys),1);
            }
        }

        forall pair | pair in JoinedWith(xs, ys, 0) + pairSetMap2(inversersionSetJoined(xs[1..], ys),1)
            ensures pair in inversersionSetJoined(xs, ys)
        {
            if pair in JoinedWith(xs, ys, 0) {
                assert pair in inversersionSetJoined(xs, ys);
            }else{
                var total := xs + ys;
                var tail := xs[1..] + ys;
                assert xs+ys == [xs[0]] + xs[1..] + ys;
                assert pair in pairSetMap2(inversersionSetJoined(xs[1..], ys),1);
                // assert pmap(pair, -1) in inversersionSetJoined(xs[1..], ys);
                var p := pmap(pair, -1);
                pairSetMap2Inverse(inversersionSetJoined(xs[1..], ys), 1, pair);
                assert p in inversersionSetJoined(xs[1..], ys);
                assert total[pair.0] == tail[p.0];
                assert total[pair.1] == tail[p.1];
                assert IsInverted(tail, p.0, p.1);
                assert IsInverted(total, pair.0, pair.1);
            }
        }
    }

    // lemma inversionSetJoinedMiddle(xs: seq<int>, ys: seq<int>, k: int)
    //     requires 0 <= k < |xs|
    //     ensures pairSetRmap(inversersionSetJoined(xs[0..k], ys), |xs|-k) + JoinedWith(xs, ys, k) + pairSetMap(inversersionSetJoined(xs[k+1..], ys),k+1) == inversersionSetJoined(xs, ys)
    // {
    //     forall x | x in inversersionSetJoined(xs, ys) 
    //         ensures x in pairSetRmap(inversersionSetJoined(xs[0..k], ys), |xs|-k) + JoinedWith(xs, ys, k) + pairSetMap(inversersionSetJoined(xs[k+1..], ys),k+1)
    //     {
    //         if x.0 < k {
    //             //[7,8,9,10,11] [1,2,3,4,5] 2 == index 6, 5 == index 9
    //             //[7,8] [1,2,3,4,5] 2 == index 3 (6-(5-2))), 5 == 6 (9-(5-2))
    //             // k == 2 (5-2==3)
    //             assert x !in JoinedWith(xs, ys, k);
    //             assert x !in pairSetMap(inversersionSetJoined(xs[k+1..], ys),k);
    //             var shortened := xs[0..k]+ys;
    //             assert |shortened| == |ys| + k;
    //             assert (xs+ys)[x.0] == (xs[0..k]+ys)[x.0];
    //             assert (xs+ys)[x.1] == (xs[0..k]+ys)[x.1-(|xs|-k)];
    //             assert IsInverted(shortened, x.0, x.1-(|xs|-k));
    //             var p := (x.0, x.1-(|xs|-k));
    //             assert x == rmap(p, |xs|-k);
    //             // assert x in inversersionSetJoined(xs[0..k], ys);
    //             assert x in pairSetRmap(inversersionSetJoined(xs[0..k], ys), |xs|-k);
    //         } else if x.0 == k {
    //             assert x in JoinedWith(xs, ys, k);
    //         } else {
    //             assert k < x.0 < |xs|+|ys|;
    //             assert x.0 < x.1 < |xs|+|ys|;
    //             var mk := pmap(x, -(k+1));
    //             assert (xs+ys)[x.0] == (xs[k+1..]+ys)[mk.0];
    //             assert (xs+ys)[x.1] == (xs[k+1..]+ys)[mk.1];
    //             // assert (xs+ys)[x.0] == (xs[k+1..]+ys)[x.0-(k+1)];
    //             // assert (xs+ys)[x.1] == (xs[k+1..]+ys)[x.1-(k+1)];
    //             assert x in pairSetMap(inversersionSetJoined(xs[k+1..], ys),k+1);
    //         }
    //     }

    //     forall x | x in pairSetRmap(inversersionSetJoined(xs[0..k], ys), |xs|-k) + JoinedWith(xs, ys, k) + pairSetMap(inversersionSetJoined(xs[k+1..], ys),k+1)
    //         ensures x in inversersionSetJoined(xs, ys)
    //     {
    //         if x in JoinedWith(xs, ys, k) {
    //             assert x in inversersionSetJoined(xs, ys);
    //         }else if x in pairSetMap(inversersionSetJoined(xs[k+1..], ys),k+1) {
    //             assert x in inversersionSetJoined(xs, ys);
    //         }else{
    //             assert x in pairSetRmap(inversersionSetJoined(xs[0..k], ys), |xs|-k);
    //             pairSetRmapInverse(inversersionSetJoined(xs[0..k], ys), |xs|-k, x);
    //             assert x in inversersionSetJoined(xs, ys);
    //         }
    //     }
    // }

    // lemma inversionSetConcatMiddle(xs: seq<int>, ys: seq<int>, k: int)
    //     requires 0 <= k < |xs|
    //     ensures pairKMap(inversersionSetJoined(xs[0..k]+xs[k+1..], ys),k,1) == inversersionSetJoined(xs, ys) - JoinedWith(xs, ys, k)
    // {
    //     inversionSetJoinedMiddle2(xs, ys, k);
    //     assert pairKMap(inversersionSetJoined(xs[0..k]+xs[k+1..], ys),k, 1) !! JoinedWith(xs, ys, k);

    // }

    lemma inversionSetJoinedMiddle2(xs: seq<int>, ys: seq<int>, k: int)
        requires 0 <= k < |xs|
        ensures JoinedWith(xs, ys, k) + pairKMap(inversersionSetJoined(xs[0..k]+xs[k+1..], ys),k,1) == inversersionSetJoined(xs, ys)
    {
        forall pair | pair in inversersionSetJoined(xs, ys)
            ensures pair in JoinedWith(xs, ys, k) + pairKMap(inversersionSetJoined(xs[0..k]+xs[k+1..], ys),k,1)
        {
            if pair.0 == k {
                assert pair in JoinedWith(xs, ys, k);
            }else if pair.0 < k {
                var mk := (pair.0, pair.1-1);
                assert mk in inversersionSetJoined(xs[0..k]+xs[k+1..], ys);
            }else{
                var mk := (pair.0-1, pair.1-1);
                assert pair in pairKMap(inversersionSetJoined(xs[0..k]+xs[k+1..], ys),k,1);
                assert mk in inversersionSetJoined(xs[0..k]+xs[k+1..], ys);
            }
        }
    }

    lemma inverionsetConcat(xs: seq<int>, ys: seq<int>)
        ensures inversionSet(xs + ys) == inversionSet(xs) + pairSetMap(inversionSet(ys), |xs|) + inversersionSetJoined(xs, ys)
    {
        var n := |xs| + |ys|;
        var xsys := xs + ys;
        assert |xsys| == n;
        assert inversionSet(xs + ys) >= inversionSet(xs) + pairSetMap(inversionSet(ys), |xs|) + inversersionSetJoined(xs, ys);
        forall pair | pair in inversionSet(xs + ys) 
            ensures pair in inversionSet(xs) + pairSetMap(inversionSet(ys), |xs|) + inversersionSetJoined(xs, ys)
        {
            if pair in inversionSet(xs) {
                assert pair in inversionSet(xs);
                assert pair in inversionSet(xs) + pairSetMap(inversionSet(ys), |xs|) + inversersionSetJoined(xs, ys);
            }else if pair in pairSetMap(inversionSet(ys), |xs|) {
                    assert pair in pairSetMap(inversionSet(ys), |xs|);
                    assert pair in inversionSet(xs) + pairSetMap(inversionSet(ys), |xs|) + inversersionSetJoined(xs, ys);
            }else if pair in inversersionSetJoined(xs, ys) {
                assert pair in inversionSet(xs) + pairSetMap(inversionSet(ys), |xs|) + inversersionSetJoined(xs, ys);
            }else{
                if 0 <= pair.0 < |xs| && |xs| <= pair.1 < n {
                    assert pair in inversersionSetJoined(xs, ys);
                }else if 0 <= pair.0 < |xs| && 0 <= pair.1 < |xs| {
                    assert pair in inversionSet(xs);
                }else if |xs| <= pair.0 < n && |xs| <= pair.1 < n {
                    var yinversions := inversionSet(ys);
                    var ypair := (pair.0 - |xs|, pair.1 - |xs|);
                    assert ypair in yinversions;
                    assert pair in pairSetMap(inversionSet(ys), |xs|);
                }
                assert false;
            }
        }
    }

    lemma inverionsetConcatSizes(xs: seq<int>, ys: seq<int>)
        ensures |inversionSet(xs + ys)| == |inversionSet(xs)| + |pairSetMap(inversionSet(ys), |xs|)| + |inversersionSetJoined(xs, ys)|
    {
        inverionsetConcat(xs, ys);
    }

    lemma {:vcs_split_on_every_assert} JoinedWithConcat(xs: seq<int>, ys: seq<int>, k: int)
        requires 0 <= k < |xs|
        ensures ys == [] ==> JoinedWith(xs, ys, k) == {}
        ensures ys != [] && IsInverted(xs+ys, k, |xs|) ==> JoinedWith(xs, ys, k) == {(k, |xs|)}+ pairSetRmap(JoinedWith(xs, ys[1..], k),1)
        ensures ys != [] && !IsInverted(xs+ys, k, |xs|) ==> JoinedWith(xs, ys, k) == pairSetRmap(JoinedWith(xs, ys[1..], k),1)
    {
        if ys == [] {
            assert JoinedWith(xs, ys, k) == {};
        }else{
            if IsInverted(xs + ys, k, |xs|) {
                assert ys == [ys[0]] + ys[1..];
                assert (xs + ys)[|xs|] == ys[0];
                forall pair | pair in JoinedWith(xs, ys[1..], k)
                    ensures rmap(pair, 1) in JoinedWith(xs, ys, k)
                {
                }
                assert (k, |xs|) in JoinedWith(xs, ys, k);
                var rest := JoinedWith(xs, ys, k)-{(k, |xs|)};
                forall pair | pair in rest
                    ensures rmap(pair,-1) in JoinedWith(xs, ys[1..], k)
                {}
                assert rest == pairSetRmap(JoinedWith(xs, ys[1..], k), 1) by {
                    forall pair | pair in pairSetRmap(JoinedWith(xs, ys[1..], k), 1)
                        ensures pair in rest
                    {
                        pairSetRmapInverse(JoinedWith(xs, ys[1..], k), 1, pair);
                    }

                    forall pair | pair in rest
                        ensures pair in pairSetRmap(JoinedWith(xs, ys[1..], k), 1)
                    {
                    }
                }
                assert JoinedWith(xs, ys, k) == {(k, |xs|)}+pairSetRmap(JoinedWith(xs, ys[1..], k), 1);
            }else{

                assert ys == [ys[0]] + ys[1..];
                assert JoinedWith(xs, ys, k) == pairSetRmap(JoinedWith(xs, ys[1..], k), 1) by {
                    forall pair | pair in pairSetRmap(JoinedWith(xs, ys[1..], k),1)
                        ensures pair in JoinedWith(xs, ys, k)
                    {
                        assert pair == rmap((pair.0, pair.1-1),1);
                        pairSetRmapInverse(JoinedWith(xs, ys[1..], k), 1, pair);
                        assert (pair.0, pair.1-1) in JoinedWith(xs, ys[1..], k);
                        assert (xs + ys)[pair.0] == (xs+ys[1..])[pair.0];
                        assert (xs + ys)[pair.1] == (xs+ys[1..])[pair.1-1];
                        assert IsInverted(xs + ys, k, pair.1);
                    }

                    forall pair | pair in JoinedWith(xs, ys, k)
                        ensures pair in pairSetRmap(JoinedWith(xs, ys[1..], k),1)
                    {
                        if pair == (k, |xs|) {
                            assert pair !in JoinedWith(xs, ys, k);
                        }else{
                            assert pair in JoinedWith(xs, ys, k);
                            assert |xs| < pair.1 < |xs| + |ys|;
                            assert |xs| <= pair.1-1 < |xs| + |ys[1..]|;
                            assert IsInverted(xs + ys[1..], k, pair.1-1);
                            assert (k, pair.1-1) in JoinedWith(xs, ys[1..], k);
                            assert rmap((k, pair.1-1), 1) == pair;
                        }
                            
                    }
                }
                assert JoinedWith(xs, ys, k) == pairSetRmap(JoinedWith(xs, ys[1..], k),1);
            }
        }
    }

    lemma  JoinedWithSame(xs: seq<int>, ys: seq<int>, k: int)
        requires 0 <= k < |xs|
        ensures JoinedWith(xs, ys, k) == JoinedWith2(xs, ys, k)
    {
        if ys == [] {
            assert JoinedWith(xs, ys, k) == {};
            assert JoinedWith2(xs, ys, k) == {};
        }else{
            if IsInverted(xs + ys, k, |xs|) {
                assert ys == [ys[0]] + ys[1..];
                assert (xs + ys)[|xs|] == ys[0];
                assert JoinedWith2(xs, ys, k) == {(k, |xs|)}+pairSetRmap(JoinedWith2(xs, ys[1..], k), 1);
                JoinedWithSame(xs, ys[1..], k);
                assert (k, |xs|) in JoinedWith2(xs, ys, k);
                assert (k, |xs|) in JoinedWith(xs, ys, k);
                JoinedWithConcat(xs, ys, k);
                assert JoinedWith(xs, ys, k) == JoinedWith2(xs, ys, k);
            }else{
                JoinedWithConcat(xs, ys, k);
                assert JoinedWith2(xs, ys, k) == pairSetRmap(JoinedWith2(xs, ys[1..], k),1);
            }

        }
    }

    lemma  JoinedWithSplit(xs: seq<int>, ys: seq<int>, i: int, k: int)
        requires xs != []
        requires 0 <= k < |xs|
        requires 0 <= i <= |ys|
        ensures JoinedWith(xs, ys, k) == JoinedWith(xs, ys[..i], k) + pairSetRmap(JoinedWith(xs, ys[i..], k), |ys[..i]|)
        ensures JoinedWith(xs, ys[..i], k) !! pairSetRmap(JoinedWith(xs, ys[i..], k), |ys[..i]|)
    {
        assert ys == ys[..i]+ys[i..];
        assert xs+ys == xs+ys[..i]+ys[i..];
        assert forall x :: x in JoinedWith(xs, ys, k) ==> x.1 < |xs|+i || x.1 >= |xs|+i;
        forall pair | pair in JoinedWith(xs, ys, k)
            ensures pair in JoinedWith(xs, ys[..i], k) + pairSetRmap(JoinedWith(xs, ys[i..], k), |ys[..i]|)
        {
            if pair.1 < |xs|+i {
                assert pair in JoinedWith(xs, ys[..i], k);
            }else{
                var yi := pair.1-|ys[..i]|;  
                assert rmap((pair.0, yi), |ys[..i]|) == pair;
                assert pair in pairSetRmap(JoinedWith(xs, ys[i..], k), |ys[..i]|);
            }
        }

        forall pair | pair in JoinedWith(xs, ys[..i], k) + pairSetRmap(JoinedWith(xs, ys[i..], k), |ys[..i]|)
            ensures pair in JoinedWith(xs, ys, k)
        {
            if pair in JoinedWith(xs, ys[..i], k) {
                assert pair in JoinedWith(xs, ys, k);

            }else{
                // assert pair !in JoinedWith(xs, ys[..i], k);
                // assert pair in pairSetRmap(JoinedWith(xs, ys[i..], k), |ys[..i]|);
                pairSetRmapInverse(JoinedWith(xs, ys[i..], k), |ys[..i]|, pair);
                assert pair in JoinedWith(xs, ys, k);

            }
        }
        assert JoinedWith(xs, ys[..i], k) !! pairSetRmap(JoinedWith(xs, ys[i..], k), |ys[..i]|) by {
            forall x | x in JoinedWith(xs, ys[..i], k)
                ensures x !in pairSetRmap(JoinedWith(xs, ys[i..], k), |ys[..i]|)
            {
                assert x.1 < |xs|+i;
                assert |ys[..i]| == i;
                assert forall y :: y in pairSetRmap(JoinedWith(xs, ys[i..], k), |ys[..i]|) ==> y.1 >= |xs|+i by {
                    forall y | y in pairSetRmap(JoinedWith(xs, ys[i..], k), |ys[..i]|) 
                        ensures y.1 >= |xs|+|ys[..i]|
                    {
                        pairSetRmapInverse(JoinedWith(xs, ys[i..], k), i, y);
                        var jj := rmap(y, -i);
                        assert |xs| <= jj.1 < |xs|+|ys[i..]|;
                        assert y == rmap(jj, i);
                        assert |xs|+i <= y.1 < |xs|+|ys|;

                    }
                }
            }
        }
    }

    lemma JoinedWithConcatSeq(xs: seq<int>, ys: seq<int>, ws: seq<int>, k: int)
        requires xs != []
        requires 0 <= k < |xs|
        ensures JoinedWith(xs, ys+ws, k) == JoinedWith(xs, ys, k) + JoinedWith(xs+ys, ws, k)
    {
        assert (xs+ys)+ws == xs+(ys+ws);
    }
    
    lemma JoinedWith4Concat(xs: seq<int>, ys: seq<int>, ws: seq<int>, k: int)
        requires xs != []
        requires 0 <= k < |xs|
        ensures JoinedWith2(xs, ys+ws, k) == JoinedWith2(xs, ys, k) + JoinedWith2(xs+ys, ws, k)
    {
        JoinedWithSame(xs, ys+ws, k);
        JoinedWithSame(xs, ys, k);
        JoinedWithSame(xs+ys, ws, k);
        JoinedWithConcatSeq(xs, ys, ws, k);
    }

    lemma  pairSetRmapAdd(ss: set<(int, int)>, yy: set<(int,int)>, i: int )
        requires ss !! yy
        ensures pairSetRmap(ss+yy, i) == pairSetRmap(ss, i) + pairSetRmap(yy, i)
    {
        forall pair | pair in pairSetRmap(ss+yy, i)
            ensures pair in pairSetRmap(ss, i) + pairSetRmap(yy, i)
        {
           pairSetRmapInverse(ss+yy, i, pair); 
        }

        forall pair | pair in pairSetRmap(ss, i) + pairSetRmap(yy, i)
            ensures pair in pairSetRmap(ss+yy, i)
        {
            if pair in pairSetRmap(ss, i) {
                pairSetRmapInverse(ss, i, pair); 
            }else { 
                pairSetRmapInverse(yy, i, pair); 
            }

        }
    }
    lemma pairSetRmapNest(ss: set<(int, int)>, i: int, k: int )
        ensures pairSetRmap(pairSetRmap(ss,i),k) == pairSetRmap(ss,i+k)
    {
        forall pair | pair in pairSetRmap(pairSetRmap(ss,i),k) 
            ensures pair in pairSetRmap(ss, i+k)
        {
            pairSetRmapInverse(pairSetRmap(ss,i),k, pair);
            var ipair := rmap(pair, -k);
            assert ipair in pairSetRmap(ss,i);
            pairSetRmapInverse(ss, i, ipair);
            var ikpair := rmap(pair, -(i+k));
            assert ikpair in ss;
            assert rmap(ikpair, i+k) == pair;
        }

        forall pair | pair in pairSetRmap(ss, i+k) 
            ensures pair in pairSetRmap(pairSetRmap(ss,i),k)
        {
            pairSetRmapInverse(ss, i+k, pair);
            var qpair := rmap(pair, -(i+k));
            assert qpair in ss;
            var ipair := rmap(qpair, i);
            assert ipair in pairSetRmap(ss,i);
            var ikpair := rmap(ipair, k);
            assert ikpair in pairSetRmap(pairSetRmap(ss,i),k);
            assert ikpair == pair;
        }
    }

    lemma {:vcs_split_on_every_assert} joinedWithRest(xs: seq<int>, ys: seq<int>, k: int, i: int)
        requires xs != []
        requires ys != []
        requires 0 <= k < |xs|
        requires 0 <= i < |ys|
        ensures |pairSetRmap(JoinedWith(xs, ys[i+1..], k),  1+|ys[..i]|)| == |JoinedWith(xs+ys[..i], ys[i+1..], k)|
    {
        assert ys == ys[..i]+[ys[i]]+ys[i+1..];
        forall pair | pair in pairSetRmap(JoinedWith(xs, ys[i+1..], k),  |ys[..i]|)
            ensures pair in JoinedWith(xs+ys[..i], ys[i+1..], k) 
        {
            assert |ys[..i]|+|ys[i+1..]| == |ys|-1;
            assert |ys[..i]|+1 == i+1;
            var rest := xs + ys[..i]+ys[i+1..];
            pairSetRmapInverse(JoinedWith(xs, ys[i+1..], k), |ys[..i]|, pair);
            var qpair := rmap(pair, -(i));
            assert qpair in JoinedWith(xs, ys[i+1..], k);
            assert |xs| <= qpair.1 < |xs|+|ys[i+1..]|;
            assert |xs|+i <= pair.1 < |xs|+i+|ys[i+1..]|;
            assert rest[pair.0] == (xs+ys[i+1..])[pair.0];
            assert rest[pair.1] == (xs+ys[i+1..])[qpair.1];
            assert IsInverted(rest, k, pair.1);
            assert (pair.0, pair.1) in JoinedWith(xs+ys[..i], ys[i+1..], k);
            // assert 
        }

        forall pair | pair in JoinedWith(xs+ys[..i], ys[i+1..], k)
            ensures pair in pairSetRmap(JoinedWith(xs, ys[i+1..], k),  |ys[..i]|) 
        {
            var rest := xs+ys[..i]+ys[i+1..];
            assert |ys[..i]| == i;
            assert |xs|+i <= pair.1 < |xs|+ i+|ys[i+1..]|;
            var qpair := rmap(pair, -|ys[..i]|);
            assert rest[pair.0] == (xs+ys[i+1..])[qpair.0];
            assert rest[pair.1] == (xs+ys[i+1..])[qpair.1];
            assert qpair in JoinedWith(xs, ys[i+1..], k);
            assert IsInverted(xs+ys[i+1..], k, qpair.1);
            assert rmap(qpair, i) == pair;

        }
        pairSetRmapLemma(JoinedWith(xs, ys[i+1..], k), |ys[..i]|);
        pairSetRmapLemma(JoinedWith(xs, ys[i+1..], k), 1+|ys[..i]|);
        assert pairSetRmap(JoinedWith(xs, ys[i+1..], k),  |ys[..i]|) == JoinedWith(xs+ys[..i], ys[i+1..], k);
    }

    lemma {:vcs_split_on_every_assert} JoinedWithMS(xs: seq<int>, ys: seq<int>, k: int, i: int)
        requires xs != []
        requires 0 <= k < |xs|
        requires 0 <= i < |ys|
        ensures IsInverted(xs+ys, k, |xs|+i) ==> |JoinedWith(xs, ys, k)| == |JoinedWith(xs, ys[0..i] + ys[i+1..], k)| + 1
        ensures !IsInverted(xs+ys, k, |xs|+i) ==> |JoinedWith(xs, ys, k)| == |JoinedWith(xs, ys[0..i] + ys[i+1..], k)|
    {
        if ys == [] {
        assert IsInverted(xs+ys, k, |xs|+i) ==> |JoinedWith(xs, ys, k)| == |JoinedWith(xs, ys[0..i] + ys[i+1..], k)| + 1;
        assert !IsInverted(xs+ys, k, |xs|+i) ==> |JoinedWith(xs, ys, k)| == |JoinedWith(xs, ys[0..i] + ys[i+1..], k)|;
        }else{
            assert ys == ys[0..i]+[ys[i]]+ys[i+1..];
            assert ys[i..] == [ys[i]]+ys[i+1..];
            JoinedWithConcatSeq(xs, ys[..i], ys[i+1..], k);
            if IsInverted(xs+ys, k, |xs|+i) {
                assert (xs+ys)[|xs|+i] == ys[i];
                assert (xs+[ys[i]])[|xs|+0] == ys[i];
                JoinedWithSplit(xs, ys, i, k);
                assert |ys[i..]| > 0;
                JoinedWithSplit(xs, ys[i..], 1, k);
                assert JoinedWith(xs, [ys[i]], k) == {(k, |xs|)};
                assert pairSetRmap(JoinedWith(xs, [ys[i]], k), |ys[..i]|) == {(k, |xs|+i)};
                assert |pairSetRmap(JoinedWith(xs, [ys[i]], k), |ys[..i]|)| ==1;
                assert JoinedWith(xs, [ys[i]], k) !! pairSetRmap(JoinedWith(xs, ys[i+1..], k), 1) by {
                    forall x | x in pairSetRmap(JoinedWith(xs, ys[i+1..], k), 1) 
                        ensures x !in JoinedWith(xs, [ys[i]], k)
                    {
                        pairSetRmapInverse(JoinedWith(xs, ys[i+1..], k), 1, x);
                        var pair := rmap(x, -1);
                        assert pair in JoinedWith(xs, ys[i+1..], k);
                        assert |xs| <= pair.1 < |xs|+|ys[i+1..]|;
                        assert x.1 >= |xs|+1;
                    }
                }
                assert JoinedWith(xs, ys[..i], k) !! pairSetRmap(JoinedWith(xs, ys[i+1..], k), 1 + |ys[..i]|) by {
                    forall x | x in JoinedWith(xs, ys[..i], k)
                        ensures x !in pairSetRmap(JoinedWith(xs, ys[i+1..], k), 1 + |ys[..i]|)
                    {
                        if x in pairSetRmap(JoinedWith(xs, ys[i+1..], k), 1 + |ys[..i]|) {

                            pairSetRmapInverse(JoinedWith(xs, ys[i+1..], k), 1 + |ys[..i]|, x);
                        }

                    }
                }
                assert JoinedWith(xs, ys[..i], k) !! pairSetRmap(JoinedWith(xs, [ys[i]], k), |ys[..i]|) by {
                    forall x | x in JoinedWith(xs, ys[..i], k)
                        ensures x !in pairSetRmap(JoinedWith(xs, [ys[i]], k), |ys[..i]|)
                    {
                        if x in pairSetRmap(JoinedWith(xs, [ys[i]], k), |ys[..i]|) {

                            pairSetRmapInverse(JoinedWith(xs, [ys[i]], k), |ys[..i]|, x);
                        }

                    }
                }
                assert pairSetRmap(JoinedWith(xs, ys[i+1..], k), 1 + |ys[..i]|) !! pairSetRmap(JoinedWith(xs, [ys[i]], k), |ys[..i]|) by {
                    forall x | x in pairSetRmap(JoinedWith(xs, ys[i+1..], k), 1 + |ys[..i]|)
                        ensures x !in pairSetRmap(JoinedWith(xs, [ys[i]], k), |ys[..i]|)
                    {
                        if x in pairSetRmap(JoinedWith(xs, [ys[i]], k), |ys[..i]|) {
                            pairSetRmapInverse(JoinedWith(xs, [ys[i]], k), |ys[..i]|,x);
                        }
                    }
                }
                calc {
                    JoinedWith(xs, ys, k);
                    JoinedWith(xs, ys[..i], k) + pairSetRmap(JoinedWith(xs, ys[i..], k), |ys[..i]|);
                    JoinedWith(xs, ys[..i], k) + pairSetRmap(JoinedWith(xs, [ys[i]], k) + pairSetRmap(JoinedWith(xs, ys[i+1..], k), 1), |ys[..i]|);
                    {pairSetRmapAdd(JoinedWith(xs, [ys[i]], k), pairSetRmap(JoinedWith(xs, ys[i+1..], k), 1) , |ys[..i]|);}
                    JoinedWith(xs, ys[..i], k) + pairSetRmap(JoinedWith(xs, [ys[i]], k), |ys[..i]|) + pairSetRmap(pairSetRmap(JoinedWith(xs, ys[i+1..], k), 1), |ys[..i]|);
                    {pairSetRmapNest(JoinedWith(xs, ys[i+1..], k),1,|ys[..i]|);}
                    JoinedWith(xs, ys[..i], k) + pairSetRmap(JoinedWith(xs, [ys[i]], k), |ys[..i]|) + pairSetRmap(JoinedWith(xs, ys[i+1..], k), 1 + |ys[..i]|);
                    JoinedWith(xs, ys[..i], k) + pairSetRmap(JoinedWith(xs, ys[i+1..], k), 1 + |ys[..i]|) + pairSetRmap(JoinedWith(xs, [ys[i]], k), |ys[..i]|);
                }
                calc {
                    |JoinedWith(xs, ys, k)|;
                    {assert JoinedWith(xs, ys, k)  == JoinedWith(xs, ys[..i], k) + pairSetRmap(JoinedWith(xs, ys[i+1..], k), 1 + |ys[..i]|) + pairSetRmap(JoinedWith(xs, [ys[i]], k), |ys[..i]|);}
                    |JoinedWith(xs, ys[..i], k) + pairSetRmap(JoinedWith(xs, ys[i+1..], k), 1 + |ys[..i]|) + pairSetRmap(JoinedWith(xs, [ys[i]], k), |ys[..i]|)|;
                    |JoinedWith(xs, ys[..i], k)| + |pairSetRmap(JoinedWith(xs, ys[i+1..], k), 1 + |ys[..i]|) + pairSetRmap(JoinedWith(xs, [ys[i]], k), |ys[..i]|)|;
                    |JoinedWith(xs, ys[..i], k)| + |pairSetRmap(JoinedWith(xs, ys[i+1..], k), 1 + |ys[..i]|)| + |pairSetRmap(JoinedWith(xs, [ys[i]], k), |ys[..i]|)|;
                    |JoinedWith(xs, ys[..i], k)| + |pairSetRmap(JoinedWith(xs, ys[i+1..], k), 1 + |ys[..i]|)| + 1;
                    {joinedWithRest(xs, ys, k, i);}
                    |JoinedWith(xs, ys[..i], k)|+|JoinedWith(xs+ys[..i], ys[i+1..], k)|+1;
                }
            }else{
                assert JoinedWith(xs, [ys[i]], k) == {};
                assert pairSetRmap(JoinedWith(xs, [ys[i]], k), |ys[..i]|) == {};
                assert |pairSetRmap(JoinedWith(xs, [ys[i]], k), |ys[..i]|)| ==0;
                JoinedWithSplit(xs, ys, i, k);
                assert |ys[i..]| > 0;
                JoinedWithSplit(xs, ys[i..], 1, k);
                assert pairSetRmap(JoinedWith(xs, ys[i+1..], k), 1 + |ys[..i]|) + pairSetRmap(JoinedWith(xs, [ys[i]], k), |ys[..i]|) == pairSetRmap(JoinedWith(xs, ys[i+1..], k), 1 + |ys[..i]|);

                calc {
                    JoinedWith(xs, ys, k);
                    JoinedWith(xs, ys[..i], k) + pairSetRmap(JoinedWith(xs, ys[i..], k), |ys[..i]|);
                    JoinedWith(xs, ys[..i], k) + pairSetRmap(JoinedWith(xs, [ys[i]], k) + pairSetRmap(JoinedWith(xs, ys[i+1..], k), 1), |ys[..i]|);
                    {pairSetRmapAdd(JoinedWith(xs, [ys[i]], k), pairSetRmap(JoinedWith(xs, ys[i+1..], k), 1) , |ys[..i]|);}
                    JoinedWith(xs, ys[..i], k) + pairSetRmap(JoinedWith(xs, [ys[i]], k), |ys[..i]|) + pairSetRmap(pairSetRmap(JoinedWith(xs, ys[i+1..], k), 1), |ys[..i]|);
                    {pairSetRmapNest(JoinedWith(xs, ys[i+1..], k),1,|ys[..i]|);}
                    JoinedWith(xs, ys[..i], k) + pairSetRmap(JoinedWith(xs, [ys[i]], k), |ys[..i]|) + pairSetRmap(JoinedWith(xs, ys[i+1..], k), 1 + |ys[..i]|);
                    JoinedWith(xs, ys[..i], k) + pairSetRmap(JoinedWith(xs, ys[i+1..], k), 1 + |ys[..i]|) + pairSetRmap(JoinedWith(xs, [ys[i]], k), |ys[..i]|);
                    JoinedWith(xs, ys[..i], k) + pairSetRmap(JoinedWith(xs, ys[i+1..], k), 1 + |ys[..i]|);
                }

                assert JoinedWith(xs, ys[..i], k) !! pairSetRmap(JoinedWith(xs, ys[i+1..], k), 1+|ys[..i]|) by {
                    forall x | x in JoinedWith(xs, ys[..i], k)
                        ensures x !in pairSetRmap(JoinedWith(xs, ys[i+1..], k), 1+|ys[..i]|)
                    {
                        if x in pairSetRmap(JoinedWith(xs, ys[i+1..], k), 1+|ys[..i]|) {
                            pairSetRmapInverse(JoinedWith(xs, ys[i+1..], k), 1+|ys[..i]|, x);

                        }
                    }
                }
                calc {
                    |JoinedWith(xs, ys, k)|;
                    {assert JoinedWith(xs, ys, k)  == JoinedWith(xs, ys[..i], k) + pairSetRmap(JoinedWith(xs, ys[i+1..], k), 1 + |ys[..i]|) + pairSetRmap(JoinedWith(xs, [ys[i]], k), |ys[..i]|);}
                    |JoinedWith(xs, ys[..i], k) + pairSetRmap(JoinedWith(xs, ys[i+1..], k), 1 + |ys[..i]|) + pairSetRmap(JoinedWith(xs, [ys[i]], k), |ys[..i]|)|;
                    |JoinedWith(xs, ys[..i], k) + pairSetRmap(JoinedWith(xs, ys[i+1..], k), 1 + |ys[..i]|)|;
                    |JoinedWith(xs, ys[..i], k)| + |pairSetRmap(JoinedWith(xs, ys[i+1..], k), 1 + |ys[..i]|)| ;
                    {joinedWithRest(xs, ys, k, i);}
                    |JoinedWith(xs, ys[..i], k)|+|JoinedWith(xs+ys[..i], ys[i+1..], k)|;
                }
            }
        }
    }

    lemma JoinedWith2MS(xs: seq<int>, ys: seq<int>, k: int, i: int)
        requires xs != []
        requires 0 <= k < |xs|
        requires 0 <= i < |ys|
        ensures IsInverted(xs+ys, k, |xs|+i) ==> |JoinedWith2(xs, ys, k)| == |JoinedWith2(xs, ys[0..i] + ys[i+1..], k)| + 1
        ensures !IsInverted(xs+ys, k, |xs|+i) ==> |JoinedWith2(xs, ys, k)| == |JoinedWith2(xs, ys[0..i] + ys[i+1..], k)|
    {
        JoinedWithSame(xs, ys, k);
        JoinedWithSame(xs, ys[0..i] + ys[i+1..], k);
        JoinedWithMS(xs, ys, k, i);

    }
   

    lemma JoinedWith2CardinalityEqualForOrderedAndUnordedSeqs(xs: seq<int>, ys: seq<int>, sxs: seq<int>, sys: seq<int>, k: int)
        requires xs != []
        requires 0 <= k < |xs|
        requires multiset(xs) == multiset(sxs)
        requires multiset(ys) == multiset(sys)
        requires Sorted(sxs)
        requires Sorted(sys)
        requires sxs[0] == xs[k]
        // decreases ys
        ensures |JoinedWith2(sxs, sys, 0)| == |JoinedWith2(xs, ys, k)|
    {
        if ys == [] {
            assert multiset(ys) == multiset([]);
            assert JoinedWith2(sxs, sys, 0) == {};
            assert JoinedWith2(xs, ys, k) == {};
            assert |JoinedWith2(sxs, sys, 0)| == |JoinedWith2(xs, ys, k)|;
        }else{
            if IsInverted(xs+ys, k, |xs|) {
                assert ys == [ys[0]] + ys[1..];
                assert multiset(ys) == multiset([ys[0]]) + multiset(ys[1..]);
                assert ys[0] == (xs+ys)[|xs|];
                assert ys[0] in multiset(ys);
                assert ys[0] in sys;
                var j :| 0 <= j < |sys| && ys[0] == sys[j];
                assert sys == sys[0..j] + [ys[0]] + sys[j+1..];
                assert multiset(sys) == multiset(sys[0..j]) + multiset([ys[0]]) + multiset(sys[j+1..]);
                calc {
                    multiset(ys[1..]);
                    multiset(ys)-multiset{ys[0]};
                    multiset(sys)-multiset{ys[0]};
                }
                assert multiset(ys[1..]) == multiset(sys[0..j] + sys[j+1..]);
                assert (sxs+sys)[0] == xs[k];
                assert (sxs+sys)[|sxs|+j] == ys[0];
                assert IsInverted(sxs+sys, 0, |sxs|+j);
                JoinedWith2CardinalityEqualForOrderedAndUnordedSeqs(xs, ys[1..], sxs, sys[0..j] + sys[j+1..], k);
                assert (k, |xs|) in JoinedWith2(xs, ys, k);
                JoinedWithSame(sxs, sys, 0);
                assert (0, |sxs|+j) in JoinedWith(sxs, sys, 0);
                assert (0, |sxs|+j) in JoinedWith2(sxs, sys, 0);
                JoinedWith2MS(sxs, sys, 0, j);
                assert |JoinedWith2(sxs, sys, 0)| == 1 + |JoinedWith2(sxs, sys[0..j] + sys[j+1..], 0)|;

                pairSetRmapLemma(JoinedWith2(xs, ys[1..], k), 1);
                JoinedWith2Size(xs, ys, k);
                assert |JoinedWith2(xs, ys[1..], k)| == |pairSetRmap(JoinedWith2(xs, ys[1..], k), 1)|;
                assert JoinedWith2(xs, ys, k) == {(k, |xs|)}+pairSetRmap(JoinedWith2(xs, ys[1..], k), 1);
                assert |JoinedWith2(xs, ys, k)| == 1+|pairSetRmap(JoinedWith2(xs, ys[1..], k), 1)|;
                assert |JoinedWith2(xs, ys, k)| == 1 + |JoinedWith2(xs, ys[1..], k)|;
            assert |JoinedWith2(sxs, sys, 0)| == |JoinedWith2(xs, ys, k)|;
            }else{

                assert ys == [ys[0]] + ys[1..];
                assert multiset(ys) == multiset([ys[0]]) + multiset(ys[1..]);
                assert ys[0] in multiset(ys);
                assert ys[0] in sys;
                var j :| 0 <= j < |sys| && ys[0] == sys[j];
                assert sys == sys[0..j] + [ys[0]] + sys[j+1..];
                assert multiset(sys) == multiset(sys[0..j]) + multiset([ys[0]]) + multiset(sys[j+1..]);
                calc {
                    multiset(ys[1..]);
                    multiset(ys)-multiset{ys[0]};
                    multiset(sys)-multiset{ys[0]};
                }
                assert multiset(ys[1..]) == multiset(sys[0..j] + sys[j+1..]);
                JoinedWith2CardinalityEqualForOrderedAndUnordedSeqs(xs, ys[1..], sxs, sys[0..j] + sys[j+1..], k);
                JoinedWith2MS(sxs, sys, 0, j);
                pairSetRmapLemma(JoinedWith2(xs, ys[1..], k), 1);
                JoinedWith2Size(xs, ys, k);
                assert |JoinedWith2(xs, ys, k)| == |JoinedWith2(xs, ys[1..], k)|;
            assert |JoinedWith2(sxs, sys, 0)| == |JoinedWith2(xs, ys, k)|;

            }
        }
    }

    lemma JoinedWithHeadAndSameSameSize(xs: seq<int>, ys: seq<int>, sxs: seq<int>, sys: seq<int>, k: int)
        requires xs != []
        requires 0 <= k < |xs|
        requires multiset(xs) == multiset(sxs)
        requires multiset(ys) == multiset(sys)
        requires Sorted(sxs)
        requires Sorted(sys)
        requires sxs[0] == xs[k]
        ensures |JoinedWith(sxs, sys, 0)| == |JoinedWith(xs, ys, k)|
    {
        JoinedWith2CardinalityEqualForOrderedAndUnordedSeqs(xs, ys, sxs, sys, k);
        JoinedWithSame(sxs, sys, 0);
        JoinedWithSame(xs, ys, k);

    }

    function restPairs(left: seq<int>, i: int, j: int): set<(int, int)>
        requires 0 <= i <= |left|
    {
        set x | i <= x < |left| :: (x, |left|+j)
    }
    lemma restPairsLemma(left: seq<int>, i: int, j: int)
        requires 0 <= i <= |left|
        ensures |restPairs(left, i, j)| == |left|-i
        decreases |left|-i
    {
        if i == |left| {
            assert restPairs(left, i, j) == {};
            assert |restPairs(left, i, j)| == 0;
        }else{
            assert (i, |left|+j) in restPairs(left, i, j);
            restPairsLemma(left, i+1, j);
            assert restPairs(left, i, j) == {(i, |left|+j)} + restPairs(left, i+1, j);
        }
    }
    
    lemma InversionSetJoinMaintained(left: seq<int>, right: seq<int>, i: int, j: int, count: int, merged: seq<int>)
        requires Sorted(left)
        requires Sorted(right)
        requires 0 <= i <= |left|
        requires 0 <= j <= |right|
        requires multiset(merged) == multiset(left[0..i] + right[0..j])
        requires forall x, y :: x in merged && y in left[i..]+right[j..] ==> x <= y
        requires count == |inversersionSetJoined(left, right[0..j])|
        ensures i+j < |left|+|right| && (j == |right| || (i < |left| && left[i] <= right[j])) ==> count == |inversersionSetJoined(left, right[0..j])|
        ensures i+j < |left|+|right| && !(j == |right| || (i < |left| && left[i] <= right[j])) ==> count + |left| - i == |inversersionSetJoined(left, right[0..j+1])|
    {
        if i+j < |left|+|right| && (j >= |right| || (i < |left| && left[i] < right[j])) {
            assert i+j < |left|+|right| && (j == |right| || (i < |left| && left[i] < right[j])) ==> count == |inversersionSetJoined(left, right[0..j])|;
        }else if i+j < |left|+|right| && !(j >= |right| || (i < |left| && left[i] < right[j])) {
            assert j < |right|;
            assert !(i < |left| && left[i] < right[j]);
            assert i == |left| || left[i] >= right[j];
            assert forall x :: x in inversersionSetJoined(left, right[0..j]) ==> x in inversersionSetJoined(left, right[0..j+1]);
            if i == |left| {
                assert |left| - i == 0;
                assert right[j] in left[i..]+right[j..];
                assert forall k :: 0 <= k < |left| ==> !IsInverted(left+right[0..j+1], k, |left|+j) by {
                    forall k | 0 <=k < |left|
                        ensures !IsInverted(left+right[0..j+1], k, |left|+j)
                    {
                        assert left[0..i] == left;
                        var slice := left+right[0..j+1];
                        assert slice[k] in multiset(left[0..i] + right[0..j]);
                        assert slice[k] in merged;
                    }
                }
                assert forall x :: x in inversersionSetJoined(left, right[0..j+1]) ==> x in inversersionSetJoined(left, right[0..j]) by {
                    forall x |  x in inversersionSetJoined(left, right[0..j+1])
                        ensures x in inversersionSetJoined(left, right[0..j])
                    {
                        if x.1 == |left|+j {
                            assert 0 <= x.0 < |left|;
                            assert IsInverted(left+right[0..j+1], x.0, |left|+j);
                            assert false;
                        }else{

                        }
                    }
                }
                assert inversersionSetJoined(left, right[0..j]) == inversersionSetJoined(left, right[0..j+1]);
                assert count + |left| - i == |inversersionSetJoined(left, right[0..j+1])|;
            }else if left[i] > right[j] {
                assert forall x :: x in inversersionSetJoined(left, right[0..j]) ==> x in inversersionSetJoined(left, right[0..j+1]);
                //assert |inversersionSetJoined(left, right[0..j+1])| >= |inversersionSetJoined(left, right[0..j])|;
                var newpairs := restPairs(left, i, j);
                restPairsLemma(left, i, j);
                assert |newpairs| == |left| - i;
                assert newpairs !! inversersionSetJoined(left, right[0..j]);
                assert |newpairs + inversersionSetJoined(left, right[0..j])| == count + |left|-i;
                assert forall x :: x in newpairs + inversersionSetJoined(left, right[0..j]) ==> x in inversersionSetJoined(left, right[0..j+1]) by {
                    forall x | x in newpairs + inversersionSetJoined(left, right[0..j])
                        ensures x in inversersionSetJoined(left, right[0..j+1])
                    {
                        if x in newpairs  {
                            assert i <= x.0 < |left|;
                            assert x.1 == |left|+j;
                            assert left[x.0] == (left+right[0..j+1])[x.0];
                            assert left[i] <= left[x.0];
                            assert left[x.0] > right[j];
                            assert IsInverted(left+right[0..j+1], x.0, x.1);
                            assert x in inversersionSetJoined(left, right[0..j+1]);
                        }else{
                            assert x in inversersionSetJoined(left, right[0..j+1]);
                        }

                    }
                }
                assert forall x :: x in inversersionSetJoined(left, right[0..j+1]) ==> x in newpairs +inversersionSetJoined(left, right[0..j]) by {
                    forall x | x in inversersionSetJoined(left, right[0..j+1])
                        ensures x in newpairs + inversersionSetJoined(left, right[0..j])
                    {
                        if x.1 == |left|+j {
                            assert x.0 >= i by {
                                if x.0 < i {
                                    assert right[j] in left[i..]+right[j..];
                                    assert left[x.0] in left[0..i] + right[0..j];
                                    assert left[x.0] in multiset(merged);
                                    assert left[x.0] in merged;
                                    assert left[x.0] <= right[j];
                                }
                            }
                            assert x in newpairs;
                        }else {
                            assert x in inversersionSetJoined(left, right[0..j]);
                        }
                    }
                }
                assert newpairs +inversersionSetJoined(left, right[0..j]) == inversersionSetJoined(left, right[0..j+1]);
                assert count + |left| - i == |inversersionSetJoined(left, right[0..j+1])|;
            }
        }
    }

    lemma PiecesEqual(xs: seq<int>, ys: seq<int>, sxs: seq<int>, sys: seq<int>, k: int)
        requires multiset(xs) == multiset(sxs)
        requires multiset(ys) == multiset(sys)
        requires Sorted(sxs)
        requires Sorted(sys)
        requires |sxs| > 0
        requires |sxs| == |xs|
        requires 0 <= k < |xs| && xs[k] == sxs[0]
        requires |inversersionSetJoined(xs[0..k] + xs[k+1..], ys)| == |inversersionSetJoined(sxs[1..], sys)|
        ensures |pairKMap(inversersionSetJoined(xs[0..k] + xs[k+1..], ys), k, 1)| == |pairSetMap2(inversersionSetJoined(sxs[1..], sys), 1)|
    {
        pairSetMap2Lemma(inversersionSetJoined(sxs[1..], sys),1);
        pairKMapSize(inversersionSetJoined(xs[0..k] + xs[k+1..], ys), k, 1);
    }

    lemma  inversetConcatOrderedUnorderedSame(xs: seq<int>, ys: seq<int>, sxs: seq<int>, sys: seq<int>)
        requires multiset(xs) == multiset(sxs)
        requires multiset(ys) == multiset(sys)
        requires Sorted(sxs)
        requires Sorted(sys)
        ensures |inversersionSetJoined(xs, ys)| == |inversersionSetJoined(sxs, sys)|
    {
        var n := |xs| + |ys|;
        var xsys := xs + ys;
        assert |xsys| == n;
        var sxsys := sxs + sys;
        seqMsLength(xs, sxs);
        seqMsLength(ys, sys);
        assert |sxsys| == n;
        assert multiset(xsys) == multiset(sxsys);
        var invs := inversersionSetJoined(xs, ys);
        if sxs == [] {
            assert xs == [];
            assert inversersionSetJoined(xs, ys) == {};
            assert |inversersionSetJoined(xs, ys)| == 0;
            assert |inversersionSetJoined(xs, ys)| == |inversersionSetJoined(sxs, sys)|;
        }else {
            assert |sxs| > 0;
            var x := sxs[0];
            assert sxs == [x] + sxs[1..];
            assert x in multiset(xs);
            var k :| 0 <= k < |xs| && x == xs[k];
            assert xs == xs[0..k] + [x] + xs[k+1..];
            assert multiset(xs) == multiset(xs[0..k] + [x] + xs[k+1..]);
            calc {
                multiset(sxs[1..]);
                multiset(sxs)-multiset{x};
                multiset(xs)-multiset{x};
                multiset(xs[0..k] + xs[k+1..]);
            }
            assert multiset(xs[0..k] + xs[k+1..]) == multiset(sxs[1..]);
            inversetConcatOrderedUnorderedSame(xs[0..k] + xs[k+1..], ys, sxs[1..], sys);
            assert |inversersionSetJoined(xs[0..k] + xs[k+1..], ys)| == |inversersionSetJoined(sxs[1..], sys)|;
            var sortedInvs := inversersionSetJoined(sxs, sys);
            var sxsFirst := JoinedWith(sxs, sys, 0);
            inversersionSetJoinedFirsts(sxs, sys);
            assert sxsFirst + pairSetMap2(inversersionSetJoined(sxs[1..], sys),1) == inversersionSetJoined(sxs, sys);
            assert sxsFirst !! pairSetMap2(inversersionSetJoined(sxs[1..], sys),1) by {
                forall pair | pair in pairSetMap2(inversersionSetJoined(sxs[1..], sys), 1)
                    ensures pair.0 != 0
                {
                    pairSetMap2Inverse(inversersionSetJoined(sxs[1..], sys), 1, pair);
                }
            }
            assert pairSetMap2(inversersionSetJoined(sxs[1..], sys), 1) == inversersionSetJoined(sxs, sys) - sxsFirst;
            var xsRest := JoinedWith(xs, ys, k);
            inversionSetJoinedMiddle2(xs, ys, k);
            assert xsRest + pairKMap(inversersionSetJoined(xs[0..k]+xs[k+1..], ys),k,1) == inversersionSetJoined(xs, ys);
            assert xsRest !! pairKMap(inversersionSetJoined(xs[0..k]+xs[k+1..], ys),k,1);
            assert pairKMap(inversersionSetJoined(xs[0..k]+xs[k+1..], ys),k,1) == inversersionSetJoined(xs, ys) - xsRest;

            // assert xsRest <= invs;
            JoinedWithHeadAndSameSameSize(xs, ys, sxs, sys, k);
            assert |JoinedWith(sxs, sys, 0)| == |JoinedWith(xs, ys, k)|;
            assert |invs| == |xsRest| + |pairKMap(inversersionSetJoined(xs[0..k] + xs[k+1..], ys), k, 1)|;
            assert |sortedInvs| == |sxsFirst| + |pairSetMap2(inversersionSetJoined(sxs[1..], sys), 1)|;
            assert |xsRest| == |sxsFirst|;
            PiecesEqual(xs, ys, sxs, sys, k);
            assert |pairKMap(inversersionSetJoined(xs[0..k] + xs[k+1..], ys), k, 1)| == |pairSetMap2(inversersionSetJoined(sxs[1..], sys), 1)|;
            assert |invs| == |sortedInvs|;
            assert |inversersionSetJoined(xs, ys)| == |inversersionSetJoined(sxs, sys)|;
        }
        
    }
}