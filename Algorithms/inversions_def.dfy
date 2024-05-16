
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

    lemma {:vcs_split_on_every_assert} JoinedWith2Size(xs: seq<int>, ys: seq<int>, k: int)
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
                        // assert rmap((k, |xs|), -1) in JoinedWith2(xs, ys[1..], k);
                        // assert rmap((k, |xs|), -1) in pairSetRmap(JoinedWith2(xs, ys[1..], k), 1);
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
    {
        (set pair | pair in ss && pair.0 < k :: (pair.0, pair.1 + i)) +
        set pair | pair in ss && pair.0 >= k :: (pair.0 + i, pair.1 + i)
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

    lemma forallPartial(xs: seq<int>, i: int, j: int) 
        requires 0 <= i < j < |xs|
        ensures forall pair :: pair in inversionSetRowPartial(xs, i, j) ==> IsInverted(xs, pair.0, pair.1)
    {}

    lemma partial(xs: seq<int>, i: int , j: int)
        requires 0 <= i < j < |xs|
        ensures IsInverted(xs, i, j) ==> inversionSetRowPartial(xs, i, j+1) == inversionSetRowPartial(xs, i, j) + {(i,j)}
        ensures !IsInverted(xs, i, j) ==> inversionSetRowPartial(xs, i, j+1) == inversionSetRowPartial(xs, i, j)
    {
        // var test := set k | 0 <= i < k < j+1 <= |xs| && proper(xs, (i, k), j+1) && IsInverted(xs, i, k) :: (i, k);
        var most := inversionSetRowPartial(xs, i, j);
        var test := set k | 0 <= i < k < j+1 <= |xs|  && IsInverted(xs, i, k) :: (i, k);
        assert test == inversionSetRowPartial(xs, i, j+1);
        if IsInverted(xs, i, j) {
            assert (i, j) !in inversionSetRowPartial(xs, i, j);
            assert (i, j) !in most;
            assert i < j < j+1 <= |xs|;
            assert IsInverted(xs, i, j) && (i,j) in test;
            assert forall x :: x in most ==> x in test;
            assert most < test;
            assert most + {(i,j)} == test;
        }else{
            assert forall x :: x in most ==> x in test;
            assert most <= test;
            // assert inversionSetRowPartial(xs, i, j+1) == inversionSetRowPartial(xs, i, j);
        }
    }

    lemma inversionSetPartialLemma(xs: seq<int>, i: int)
        requires 0 <= i < |xs|
        ensures inversionSetPartial(xs, i+1) == inversionSetPartial(xs, i) + inversionSetRowPartial(xs, i, |xs|)
    {
        forall x | x in inversionSetRowPartial(xs, i, |xs|)
            ensures x in inversionSetPartial(xs, i+1)
        {
            assert IsInverted(xs, x.0, x.1);
            assert x.0 == i;
            assert 0 <= x.0 < i+1 <= |xs|;
            assert x in inversionSetPartial(xs, i+1);
        }
    }

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

    lemma inversionSetJoinedMiddle(xs: seq<int>, ys: seq<int>, k: int)
        requires 0 <= k < |xs|
        ensures pairSetRmap(inversersionSetJoined(xs[0..k], ys), |xs|-k) + JoinedWith(xs, ys, k) + pairSetMap(inversersionSetJoined(xs[k+1..], ys),k+1) == inversersionSetJoined(xs, ys)
    {
        forall x | x in inversersionSetJoined(xs, ys) 
            ensures x in pairSetRmap(inversersionSetJoined(xs[0..k], ys), |xs|-k) + JoinedWith(xs, ys, k) + pairSetMap(inversersionSetJoined(xs[k+1..], ys),k+1)
        {
            if x.0 < k {
                //[7,8,9,10,11] [1,2,3,4,5] 2 == index 6, 5 == index 9
                //[7,8] [1,2,3,4,5] 2 == index 3 (6-(5-2))), 5 == 6 (9-(5-2))
                // k == 2 (5-2==3)
                assert x !in JoinedWith(xs, ys, k);
                assert x !in pairSetMap(inversersionSetJoined(xs[k+1..], ys),k);
                var shortened := xs[0..k]+ys;
                assert |shortened| == |ys| + k;
                assert (xs+ys)[x.0] == (xs[0..k]+ys)[x.0];
                assert (xs+ys)[x.1] == (xs[0..k]+ys)[x.1-(|xs|-k)];
                assert IsInverted(shortened, x.0, x.1-(|xs|-k));
                var p := (x.0, x.1-(|xs|-k));
                assert x == rmap(p, |xs|-k);
                // assert x in inversersionSetJoined(xs[0..k], ys);
                assert x in pairSetRmap(inversersionSetJoined(xs[0..k], ys), |xs|-k);
            } else if x.0 == k {
                assert x in JoinedWith(xs, ys, k);
            } else {
                assert k < x.0 < |xs|+|ys|;
                assert x.0 < x.1 < |xs|+|ys|;
                var mk := pmap(x, -(k+1));
                assert (xs+ys)[x.0] == (xs[k+1..]+ys)[mk.0];
                assert (xs+ys)[x.1] == (xs[k+1..]+ys)[mk.1];
                // assert (xs+ys)[x.0] == (xs[k+1..]+ys)[x.0-(k+1)];
                // assert (xs+ys)[x.1] == (xs[k+1..]+ys)[x.1-(k+1)];
                assert x in pairSetMap(inversersionSetJoined(xs[k+1..], ys),k+1);
            }
        }

        forall x | x in pairSetRmap(inversersionSetJoined(xs[0..k], ys), |xs|-k) + JoinedWith(xs, ys, k) + pairSetMap(inversersionSetJoined(xs[k+1..], ys),k+1)
            ensures x in inversersionSetJoined(xs, ys)
        {
            if x in JoinedWith(xs, ys, k) {
                assert x in inversersionSetJoined(xs, ys);
            }else if x in pairSetMap(inversersionSetJoined(xs[k+1..], ys),k+1) {
                assert x in inversersionSetJoined(xs, ys);
            }else{
                assert x in pairSetRmap(inversersionSetJoined(xs[0..k], ys), |xs|-k);
                pairSetRmapInverse(inversersionSetJoined(xs[0..k], ys), |xs|-k, x);
                assert x in inversersionSetJoined(xs, ys);
            }
        }
    }

    lemma inversionSetConcatMiddle(xs: seq<int>, ys: seq<int>, k: int)
        requires 0 <= k < |xs|
        ensures pairKMap(inversersionSetJoined(xs[0..k]+xs[k+1..], ys),k,1) == inversersionSetJoined(xs, ys) - JoinedWith(xs, ys, k)
    {
        inversionSetJoinedMiddle2(xs, ys, k);
        assert pairKMap(inversersionSetJoined(xs[0..k]+xs[k+1..], ys),k, 1) !! JoinedWith(xs, ys, k);

    }

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
                    // assert xsys[pair.0] > xsys[pair.1];
                    // assert pair.0 < pair.1;
                    // assert pair.0 - |xs| < |ys|;
                    // assert pair.1 - |xs| < |ys|;
                    // assert ys[pair.0 - |xs|] == xsys[pair.0];
                    // assert ys[pair.1 - |xs|] == xsys[pair.1];
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
}