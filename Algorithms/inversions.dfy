include "inversions_def.dfy"
module Inversions {
    import opened InversionDefs

    lemma countInversionTest() {
        var sample := [1,3,5,2,4,6];
        assert IsInverted(sample, 2, 3);
        assert IsInverted(sample, 1, 3);
        assert IsInverted(sample, 2, 4);
        assert inversionSet(sample) == {(1,3), (2,3), (2,4)};
        // assert !IsInverted(sample, 0, 4);
        assert countInversion(sample) == 3;
    }

    //{:vcs_split_on_every_assert}
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
            assert sxsFirst <= sortedInvs;
            // assume sxsFirst !! pairSetMap2(inversersionSetJoined(sxs[1..], sys), 1);
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
            something(xs, ys, sxs, sys, k);
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



    method BruteForceCount(xs: seq<int>) returns (numInv: int)
        requires |xs| > 1
        ensures numInv == countInversion(xs)
    {
        ghost var inversions: set<(int, int)> := {};
        numInv := 0;
        for i := 0 to |xs|-1 
            invariant 0 <= i <= |xs|-1
            invariant inversions == inversionSetPartial(xs, i)
            invariant numInv == |inversions|
        {
            // assert i <= |xs|-2;
            ghost var inversionsRows: set<(int, int)> := {};
            ghost var irc := 0;
            ghost var oldnumInv := numInv;
            for j := i+1 to |xs| 
                invariant i <= |xs|-2
                invariant i+1 <= j <= |xs|
                invariant inversionSetRowPartial(xs, i, j) == inversionsRows
                invariant |inversionsRows| == irc
                invariant numInv == irc+oldnumInv
            {
                ghost var oldInversionRows := inversionsRows;
                if xs[i] > xs[j] {
                    numInv := numInv + 1;
                    inversionsRows := inversionsRows + {(i,j)};
                    irc := irc + 1;
                }
            }
            inversions := inversions + inversionsRows;
        }
        assert inversions == inversionSet(xs);
    }

// //Tim Roughgarden's algorithms illuminated part 1 page 64
    method {:verify } {:vcs_split_on_every_assert} SortAndCountInv(xs: seq<int>) returns (sortedXs: seq<int>, numInv: int)
        ensures numInv == countInversion(xs)
        ensures multiset(sortedXs) == multiset(xs)
        ensures Sorted(sortedXs)
    {
        if |xs| <= 1 {
            return xs, 0;
        }else{
            var n := |xs|;
            var m := n/2;
            var left := xs[0..m];
            var right := xs[m..];
            assert xs == left + right;
            assert multiset(left + right) == multiset(xs);
            var leftSorted, leftInv := SortAndCountInv(left);
            assert multiset(leftSorted) == multiset(left);
            var rightSorted, rightInv := SortAndCountInv(right);
            assert multiset(rightSorted) == multiset(right);
            var merged, splitInv := MergeAndCountInv(leftSorted, rightSorted);
            // assert multiset(merged) == multiset(left + right);
            // assert multiset(merged) == multiset(leftSorted + rightSorted);
            // assert multiset(merged) == multiset(xs);
            inverionsetConcat(left, right);
            inverionsetConcatSizes(left, right);
            assert countInversion(left+right) == countInversion(left) + |pairSetMap(inversionSet(right), |left|)| + |inversersionSetJoined(left, right)|;
            assert countInversion(left+right) == countInversion(xs);
            assert leftInv == countInversion(left);
            assert rightInv == countInversion(right);
            inversetConcatOrderedUnorderedSame(left, right, leftSorted, rightSorted);
            assert splitInv == |inversersionSetJoined(leftSorted, rightSorted)|;
            assert splitInv == |inversersionSetJoined(left, right)|;
            pairMapSize(right, |left|);
            assert countInversion(left+right) == leftInv + rightInv + splitInv;
            return merged, leftInv + rightInv + splitInv;
        }
    }



    method {:verify }  MergeAndCountInv(left: seq<int>, right: seq<int>) returns (merged: seq<int>, splitInv: int)
        requires Sorted(left)
        requires Sorted(right)
        ensures |merged| == |left| + |right|
        ensures multiset(merged) == multiset(left + right)
        // ensures splitInv == countInversion(merged)
        ensures splitInv == |inversersionSetJoined(left, right)|
        ensures Sorted(merged)
    {
        var n := |left| + |right|;
        var i := 0;
        var j := 0;
        var k := 0;
        ghost var inversions := inversersionSetJoined(left[0..i], right[0..j]);
        assert inversions == {};
        var inv := 0;
        merged := [];
        while k < n
            invariant 0 <= k <= n
            invariant k == i+j
            invariant 0 <= i+j <= n
            invariant 0 <= i <= |left|
            invariant 0 <= j <= |right|
            invariant |merged| == k
            // invariant inversions == inversersionSetJoined(left[0..i], right[0..j])
            // invariant inv == countInversion(merged)
            invariant multiset(merged) == multiset(left[0..i] + right[0..j])

            // invariant forall x :: 0 <= x < |merged| ==> merged[x] <= right[j];
            invariant forall x :: x in merged ==> x in left[..i] || x in right[..j]
            invariant forall x, y :: x in merged && y in left[i..]+right[j..] ==> x <= y
            invariant Sorted(merged)
            invariant inv == |inversersionSetJoined(left, right[0..j])|
        {
            assert left == left[0..i] + left[i..];
            assert right == right[0..j] + right[j..];
            print "before: i: ",i," j: ",j, " inv: ", inv," ", inversersionSetJoined(left, right[..j]), " |_|=", |inversersionSetJoined(left, right[..j])|, "\n";
            InversionSetJoinMaintained(left, right, i, j, inv, merged);
            if j >= |right| || (i < |left| && left[i] <= right[j]) {
                assert i < |left| by {
                    if i < |left| {
                        assert i < |left|;
                    }else{
                        assert j >= |right|;
                    }
                }

                // assert Sorted(merged); 
                assert forall x, y :: x in merged && y in left[i..]+right[j..] ==> x <= y;
                assert left[i] in left[i..]+right[j..];
                assert forall x :: 0 <= x < |merged| ==> merged[x] <= left[i] by {
                    forall x | 0 <= x < |merged|
                        ensures merged[x] <= left[i]
                    {
                        
                        assert merged[x] in merged;
                    }
                }
                ghost var oldmerged := merged;
                merged := merged + [left[i]];
                assert left[0..i+1] == left[0..i] + [left[i]];
                assert multiset(merged) == multiset(left[0..i+1] + right[0..j]);
                assert forall x, y :: x in merged && y in left[i+1..]+right[j..] ==> x <= y by {
                    forall x, y | x in merged && y in left[i+1..]+right[j..] 
                        ensures x <= y
                    {
                        if x in left[0..i+1] {
                            assert x <= left[i];
                            assert x <= y;
                        }else{
                            assert x in merged;
                            assert x in right[0..j];
                            var k :| 0 <= k < j <= |right| && x == right[k];
                            assert k < j;
                            if y in left[i+1..] {
                                assert y >= left[i]; 
                                if x == left[i] {
                                    assert x <= left[i];
                                }else if x in oldmerged {
                                    assert forall z, w :: z in oldmerged && w in left[i..]+right[j..] ==> z <= w; 
                                    assert left[i] in left[i..]+right[j..];
                                    assert x <= left[i];

                                }
                                assert x <= y;
                            }else{
                                assert y in right[j..];
                                assert x <= y;

                            }
                        }
                    }
                }
                i := i + 1;
                assert inv == |inversersionSetJoined(left, right[0..j])|;
            }else{
                // assume forall x :: 0 <= x < |merged| ==> merged[x] <= right[j];
                assert forall x :: 0 <= x < |merged| ==> merged[x] <= right[j] by {
                    assert right[j] in left[i..]+right[j..];
                    forall x | 0 <= x < |merged|
                        ensures merged[x] <= right[j]
                    {
                        assert merged[x] in merged;

                    }
                }
                assert right[0..j+1] == right[0..j] + [right[j]];
                merged := merged + [right[j]];
                assert forall x, y :: x in merged && y in left[i..]+right[j+1..] ==> x <= y;
                j := j + 1;
                assert Sorted(merged);
                inv := inv + |left| - i;
                assert inv == |inversersionSetJoined(left, right[0..j])|;
            }
            k := k + 1;
            print "after: i: ",i," j: ",j, " inv: ", inv," ", inversersionSetJoined(left, right[..j]), " |_|=", |inversersionSetJoined(left, right[..j])|, "\n";

            // assume inv == |inversersionSetJoined(left[0..i], right[0..j])|;
        }
        assert i == |left|;
        assert j == |right|;
        assert left[0..i] == left;
        assert right[0..j] == right;
        assert multiset(left[0..i]) == multiset(left);
        assert multiset(merged) == multiset(left + right);
        return merged, inv;
    }

    method Main() {
        var res1, rest := SortAndCountInv([1,2,5,6,7]+[7,8]);
        print res1;
        print rest;
    }
}
