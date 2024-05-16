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

    // {
    //     var x :| x in multiset(xs) && x in multiset(ys) && x in xs && x in ys;
    // }



    lemma {:verify } {:vcs_split_on_every_assert} JoinedWithMS(xs: seq<int>, ys: seq<int>, k: int, i: int)
        requires xs != []
        requires 0 <= k < |xs|
        requires 0 <= i < |ys|
        ensures IsInverted(xs+ys, k, |xs|+i) ==> JoinedWith(xs, ys, k) == JoinedWith(xs, ys[0..i] + ys[i+1..], k) + {(k, |xs|+i)}
        ensures !IsInverted(xs+ys, k, |xs|+i) ==> JoinedWith(xs, ys, k) == JoinedWith(xs, ys[0..i] + ys[i+1..], k)
    {
        if ys == [] {
        assert IsInverted(xs+ys, k, |xs|+i) ==> JoinedWith(xs, ys, k) == JoinedWith(xs, ys[0..i] + ys[i+1..], k) + {(k, |xs|+i)};
        assert !IsInverted(xs+ys, k, |xs|+i) ==> JoinedWith(xs, ys, k) == JoinedWith(xs, ys[0..i] + ys[i+1..], k);
        }else{
            assert ys == ys[0..i]+[ys[i]]+ys[i+1..];
            assert ys[i..] == [ys[i]]+ys[i+1..];
            if IsInverted(xs+ys, k, |xs|+i) {
                assert (xs+ys)[|xs|+i] == ys[i];
                assert (xs+[ys[i]])[|xs|+0] == ys[i];
                JoinedWithSplit(xs, ys, i, k);
                assert |ys[i..]| > 0;
                JoinedWithSplit(xs, ys[i..], 1, k);
                assert JoinedWith(xs, [ys[i]], k) == {(k, |xs|)};
                assert JoinedWith(xs, [ys[i]], k) !! pairSetRmap(JoinedWith(xs, ys[i+1..], k), 1) by {
                    forall x | x in pairSetRmap(JoinedWith(xs, ys[i+1..], k), 1) 
                        ensures x !in JoinedWith(xs, [ys[i]], k)
                    {
                        pairSetRmapInverse(JoinedWith(xs, ys[i+1..], k), 1, x);
                        var pair := rmap(x, -1);
                        assert pair in JoinedWith(xs, ys[i+1..], k);
                        assert |xs| <= pair.1 < |xs|+|ys[i+1..]|;
                        assert x.1 >= |xs|+1;
                        // assert xs+ys[i+1..] < 
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
                }
                assert JoinedWith(xs, ys, k) == JoinedWith(xs, ys[0..i] + ys[i+1..], k) + {(k, |xs|+i)};
            }else{
                assert JoinedWith(xs, ys, k) == JoinedWith(xs, ys[0..i] + ys[i+1..], k);
            }
        }
    }

//     lemma {:verify false}JoinedWith2MS(xs: seq<int>, ys: seq<int>, k: int, i: int)
//         requires xs != []
//         requires 0 <= k < |xs|
//         requires 0 <= i < |ys|
//         ensures IsInverted(xs+ys, k, |xs|+i) ==> |JoinedWith2(xs, ys, k)| == |JoinedWith2(xs, ys[0..i] + ys[i+1..], k)| + 1
//         ensures !IsInverted(xs+ys, k, |xs|+i) ==> |JoinedWith2(xs, ys, k)| == |JoinedWith2(xs, ys[0..i] + ys[i+1..], k)|
//     {
//         if |ys| == 0 {

//         }else if |ys| == 1 {

//         }else{
//             assert ys == ys[0..i] + [ys[i]] + ys[i+1..];
//             if !IsInverted(xs+ys, k, |xs|+i) {

//                 assert |JoinedWith2(xs, ys, k)| == |JoinedWith2(xs, ys[0..i] + ys[i+1..], k)|;
//             }else{
//                 assert |JoinedWith2(xs, ys, k)| == |JoinedWith2(xs, ys[0..i] + ys[i+1..], k)| + 1;

//             }
//         }
//     }
   

//     lemma {:verify } JoinedWith2CardinalityEqualForOrderedAndUnordedSeqs(xs: seq<int>, ys: seq<int>, sxs: seq<int>, sys: seq<int>, k: int)
//         requires xs != []
//         requires 0 <= k < |xs|
//         requires multiset(xs) == multiset(sxs)
//         requires multiset(ys) == multiset(sys)
//         requires Sorted(sxs)
//         requires Sorted(sys)
//         requires sxs[0] == xs[k]
//         // decreases ys
//         ensures |JoinedWith2(sxs, sys, 0)| == |JoinedWith2(xs, ys, k)|
//     {
//         if ys == [] {
//             assert multiset(ys) == multiset([]);
//             assert JoinedWith2(sxs, sys, 0) == {};
//             assert JoinedWith2(xs, ys, k) == {};
//             assert |JoinedWith2(sxs, sys, 0)| == |JoinedWith2(xs, ys, k)|;
//         }else{
//             if IsInverted(xs+ys, k, |xs|) {
//                 assert ys == [ys[0]] + ys[1..];
//                 assert multiset(ys) == multiset([ys[0]]) + multiset(ys[1..]);
//                 assert ys[0] == (xs+ys)[|xs|];
//                 assert ys[0] in multiset(ys);
//                 assert ys[0] in sys;
//                 var j :| 0 <= j < |sys| && ys[0] == sys[j];
//                 assert sys == sys[0..j] + [ys[0]] + sys[j+1..];
//                 assert multiset(sys) == multiset(sys[0..j]) + multiset([ys[0]]) + multiset(sys[j+1..]);
//                 calc {
//                     multiset(ys[1..]);
//                     multiset(ys)-multiset{ys[0]};
//                     multiset(sys)-multiset{ys[0]};
//                 }
//                 assert multiset(ys[1..]) == multiset(sys[0..j] + sys[j+1..]);
//                 assert (sxs+sys)[0] == xs[k];
//                 assert (sxs+sys)[|sxs|+j] == ys[0];
//                 assert IsInverted(sxs+sys, 0, |sxs|+j);
//                 JoinedWith2CardinalityEqualForOrderedAndUnordedSeqs(xs, ys[1..], sxs, sys[0..j] + sys[j+1..], k);
//                 assert (k, |xs|) in JoinedWith2(xs, ys, k);
//                 JoinedWithSame(sxs, sys, 0);
//                 assert (0, |sxs|+j) in JoinedWith(sxs, sys, 0);
//                 assert (0, |sxs|+j) in JoinedWith2(sxs, sys, 0);
//                 JoinedWith2MS(sxs, sys, 0, j);
//                 assert |JoinedWith2(sxs, sys, 0)| == 1 + |JoinedWith2(sxs, sys[0..j] + sys[j+1..], 0)|;

//                 pairSetRmapLemma(JoinedWith2(xs, ys[1..], k), 1);
//                 JoinedWith2Size(xs, ys, k);
//                 assert |JoinedWith2(xs, ys[1..], k)| == |pairSetRmap(JoinedWith2(xs, ys[1..], k), 1)|;
//                 assert JoinedWith2(xs, ys, k) == {(k, |xs|)}+pairSetRmap(JoinedWith2(xs, ys[1..], k), 1);
//                 assert |JoinedWith2(xs, ys, k)| == 1+|pairSetRmap(JoinedWith2(xs, ys[1..], k), 1)|;
//                 assert |JoinedWith2(xs, ys, k)| == 1 + |JoinedWith2(xs, ys[1..], k)|;
//             assert |JoinedWith2(sxs, sys, 0)| == |JoinedWith2(xs, ys, k)|;
//             }else{

//                 assert ys == [ys[0]] + ys[1..];
//                 assert multiset(ys) == multiset([ys[0]]) + multiset(ys[1..]);
//                 assert ys[0] in multiset(ys);
//                 assert ys[0] in sys;
//                 var j :| 0 <= j < |sys| && ys[0] == sys[j];
//                 assert sys == sys[0..j] + [ys[0]] + sys[j+1..];
//                 assert multiset(sys) == multiset(sys[0..j]) + multiset([ys[0]]) + multiset(sys[j+1..]);
//                 calc {
//                     multiset(ys[1..]);
//                     multiset(ys)-multiset{ys[0]};
//                     multiset(sys)-multiset{ys[0]};
//                 }
//                 assert multiset(ys[1..]) == multiset(sys[0..j] + sys[j+1..]);
//                 JoinedWith2CardinalityEqualForOrderedAndUnordedSeqs(xs, ys[1..], sxs, sys[0..j] + sys[j+1..], k);
//                 JoinedWith2MS(sxs, sys, 0, j);
//                 pairSetRmapLemma(JoinedWith2(xs, ys[1..], k), 1);
//                 JoinedWith2Size(xs, ys, k);
//                 assert |JoinedWith2(xs, ys, k)| == |JoinedWith2(xs, ys[1..], k)|;
//             assert |JoinedWith2(sxs, sys, 0)| == |JoinedWith2(xs, ys, k)|;

//             }
//         }
//     }

//     lemma {:verify } something(xs: seq<int>, ys: seq<int>, sxs: seq<int>, sys: seq<int>, k: int)
//         requires xs != []
//         requires 0 <= k < |xs|
//         requires multiset(xs) == multiset(sxs)
//         requires multiset(ys) == multiset(sys)
//         requires Sorted(sxs)
//         requires Sorted(sys)
//         requires sxs[0] == xs[k]
//         ensures |JoinedWith(sxs, sys, 0)| == |JoinedWith(xs, ys, k)|
//     {
//         JoinedWith2CardinalityEqualForOrderedAndUnordedSeqs(xs, ys, sxs, sys, k);
//         JoinedWithSame(sxs, sys, 0);
//         JoinedWithSame(xs, ys, k);

//     }

//     lemma {:verify false} {:vcs_split_on_every_assert} inversetConcatOrderedUnorderedSame(xs: seq<int>, ys: seq<int>, sxs: seq<int>, sys: seq<int>)
//         requires multiset(xs) == multiset(sxs)
//         requires multiset(ys) == multiset(sys)
//         requires Sorted(sxs)
//         requires Sorted(sys)
//         ensures |inversersionSetJoined(xs, ys)| == |inversersionSetJoined(sxs, sys)|
//     {
//         var n := |xs| + |ys|;
//         var xsys := xs + ys;
//         assert |xsys| == n;
//         var sxsys := sxs + sys;
//         seqMsLength(xs, sxs);
//         seqMsLength(ys, sys);
//         assert |sxsys| == n;
//         assert multiset(xsys) == multiset(sxsys);
//         var invs := inversersionSetJoined(xs, ys);
//         if sxs == [] {

//         }else {
//             var x := sxs[0];
//             assert sxs == [x] + sxs[1..];
//             assert x in multiset(xs);
//             var k :| 0 <= k < |xs| && x == xs[k];
//             assert xs == xs[0..k] + [x] + xs[k+1..];
//             assert multiset(xs) == multiset(xs[0..k] + [x] + xs[k+1..]);
//             calc {
//                 multiset(sxs[1..]);
//                 multiset(sxs)-multiset{x};
//                 multiset(xs)-multiset{x};
//                 multiset(xs[0..k] + xs[k+1..]);
//             }
//             assert multiset(xs[0..k] + xs[k+1..]) == multiset(sxs[1..]);
//             inversetConcatOrderedUnorderedSame(xs[0..k] + xs[k+1..], ys, sxs[1..], sys);
//             assert |inversersionSetJoined(xs[0..k] + xs[k+1..], ys)| == |inversersionSetJoined(sxs[1..], sys)|;
//             var sortedInvs := inversersionSetJoined(sxs, sys);
//             var sxsFirst := JoinedWith(sxs, sys, 0);
//             inversersionSetJoinedFirsts(sxs, sys);
//             assert sxsFirst <= sortedInvs;
//             // assume sxsFirst !! pairSetMap2(inversersionSetJoined(sxs[1..], sys), 1);
//             assert sxsFirst + pairSetMap2(inversersionSetJoined(sxs[1..], sys),1) == inversersionSetJoined(sxs, sys);
//             assert sxsFirst !! pairSetMap2(inversersionSetJoined(sxs[1..], sys),1) by {
//                 forall pair | pair in pairSetMap2(inversersionSetJoined(sxs[1..], sys), 1)
//                     ensures pair.0 != 0
//                 {
//                     pairSetMap2Inverse(inversersionSetJoined(sxs[1..], sys), 1, pair);
//                 }
//             }
//             assert pairSetMap2(inversersionSetJoined(sxs[1..], sys), 1) == inversersionSetJoined(sxs, sys) - sxsFirst;
//             var xsRest := JoinedWith(xs, ys, k);
//             inversionSetJoinedMiddle2(xs, ys, k);
//             assert xsRest + pairKMap(inversersionSetJoined(xs[0..k]+xs[k+1..], ys),k,1) == inversersionSetJoined(xs, ys);
//             assert xsRest !! pairKMap(inversersionSetJoined(xs[0..k]+xs[k+1..], ys),k,1);
//             assert pairKMap(inversersionSetJoined(xs[0..k]+xs[k+1..], ys),k,1) == inversersionSetJoined(xs, ys) - xsRest;

//             // assert xsRest <= invs;
//             something(xs, ys, sxs, sys, k);
//             assert |JoinedWith(sxs, sys, 0)| == |JoinedWith(xs, ys, k)|;
//             assert |invs| == |xsRest| + |pairKMap(inversersionSetJoined(xs[0..k] + xs[k+1..], ys), k, 1)|;
//             assert |sortedInvs| == |sxsFirst| + |pairSetMap2(inversersionSetJoined(sxs[1..], sys), 1)|;
//             // assume |pairKMap(inversersionSetJoined(xs[0..k] + xs[k+1..], ys), k, 1)| ==  |pairSetMap2(inversersionSetJoined(sxs[1..], sys), 1)|;

//             assert |inversersionSetJoined(xs, ys)| == |inversersionSetJoined(sxs, sys)|;
//         }
        
//     }



//     method BruteForceCount(xs: seq<int>) returns (numInv: int)
//         requires |xs| > 1
//         ensures numInv == countInversion(xs)
//     {
//         ghost var inversions: set<(int, int)> := {};
//         numInv := 0;
//         for i := 0 to |xs|-1 
//             invariant 0 <= i <= |xs|-1
//             invariant inversions == inversionSetPartial(xs, i)
//             invariant numInv == |inversions|
//         {
//             // assert i <= |xs|-2;
//             ghost var inversionsRows: set<(int, int)> := {};
//             ghost var irc := 0;
//             ghost var oldnumInv := numInv;
//             for j := i+1 to |xs| 
//                 invariant i <= |xs|-2
//                 invariant i+1 <= j <= |xs|
//                 invariant inversionSetRowPartial(xs, i, j) == inversionsRows
//                 invariant |inversionsRows| == irc
//                 invariant numInv == irc+oldnumInv
//             {
//                 ghost var oldInversionRows := inversionsRows;
//                 if xs[i] > xs[j] {
//                     numInv := numInv + 1;
//                     inversionsRows := inversionsRows + {(i,j)};
//                     irc := irc + 1;
//                 }
//             }
//             inversions := inversions + inversionsRows;
//         }
//         assert inversions == inversionSet(xs);
//     }

// //Tim Roughgarden's algorithms illuminated part 1 page 64
//     method {:verify } {:vcs_split_on_every_assert} SortAndCountInv(xs: seq<int>) returns (sortedXs: seq<int>, numInv: int)
//         ensures numInv == countInversion(xs)
//         ensures multiset(sortedXs) == multiset(xs)
//         ensures Sorted(sortedXs)
//     {
//         if |xs| <= 1 {
//             return xs, 0;
//         }else{
//             var n := |xs|;
//             var m := n/2;
//             var left := xs[0..m];
//             var right := xs[m..];
//             assert xs == left + right;
//             assert multiset(left + right) == multiset(xs);
//             var leftSorted, leftInv := SortAndCountInv(left);
//             assert multiset(leftSorted) == multiset(left);
//             var rightSorted, rightInv := SortAndCountInv(right);
//             assert multiset(rightSorted) == multiset(right);
//             var merged, splitInv := MergeAndCountInv(leftSorted, rightSorted);
//             // assert multiset(merged) == multiset(left + right);
//             // assert multiset(merged) == multiset(leftSorted + rightSorted);
//             // assert multiset(merged) == multiset(xs);
//             inverionsetConcat(left, right);
//             inverionsetConcatSizes(left, right);
//             assert countInversion(left+right) == countInversion(left) + |pairSetMap(inversionSet(right), |left|)| + |inversersionSetJoined(left, right)|;
//             assert countInversion(left+right) == countInversion(xs);
//             assert leftInv == countInversion(left);
//             assert rightInv == countInversion(right);
//             inversetConcatOrderedUnorderedSame(left, right, leftSorted, rightSorted);
//             assert splitInv == |inversersionSetJoined(leftSorted, rightSorted)|;
//             assert splitInv == |inversersionSetJoined(left, right)|;
//             pairMapSize(right, |left|);
//             assert countInversion(left+right) == leftInv + rightInv + splitInv;
//             return merged, leftInv + rightInv + splitInv;
//         }
//     }

//     method {:verify false} {:vcs_split_on_every_assert} MergeAndCountInv(left: seq<int>, right: seq<int>) returns (merged: seq<int>, splitInv: int)
//         requires Sorted(left)
//         requires Sorted(right)
//         ensures |merged| == |left| + |right|
//         ensures multiset(merged) == multiset(left + right)
//         // ensures splitInv == countInversion(merged)
//         ensures splitInv == |inversersionSetJoined(left, right)|
//         ensures Sorted(merged)
//     {
//         var n := |left| + |right|;
//         var i := 0;
//         var j := 0;
//         var k := 0;
//         ghost var inversions := inversersionSetJoined(left[0..i], right[0..j]);
//         assert inversions == {};
//         var inv := 0;
//         merged := [];
//         while k < n
//             invariant 0 <= k <= n
//             invariant k == i+j
//             invariant 0 <= i+j <= n
//             invariant 0 <= i <= |left|
//             invariant 0 <= j <= |right|
//             invariant |merged| == k
//             // invariant inv == countInversion(merged)
//             invariant multiset(merged) == multiset(left[0..i] + right[0..j])
//             invariant forall x :: x in merged ==> x in left[..i] || x in right[..j]
//             invariant forall x, y :: x in merged && y in left[i..]+right[j..] ==> x <= y
//             invariant Sorted(merged)
//             invariant inv == |inversersionSetJoined(left[0..i], right[0..j])|
//         {
//             assert left == left[0..i] + left[i..];
//             assert right == right[0..j] + right[j..];
//             if j >= |right| || (i < |left| && left[i] < right[j]) {
//                 assert i < |left| by {
//                     if i < |left| {
//                         assert i < |left|;
//                     }else{
//                         assert j >= |right|;
//                     }
//                 }

//                 // assert Sorted(merged); 
//                 assert forall x, y :: x in merged && y in left[i..]+right[j..] ==> x <= y;
//                 assert left[i] in left[i..]+right[j..];
//                 assert forall x :: 0 <= x < |merged| ==> merged[x] <= left[i] by {
//                     forall x | 0 <= x < |merged|
//                         ensures merged[x] <= left[i]
//                     {
                        
//                         assert merged[x] in merged;
//                     }
//                 }
//                 ghost var oldmerged := merged;
//                 merged := merged + [left[i]];
//                 assert left[0..i+1] == left[0..i] + [left[i]];
//                 assert multiset(merged) == multiset(left[0..i+1] + right[0..j]);
//                 assert forall x, y :: x in merged && y in left[i+1..]+right[j..] ==> x <= y by {
//                     forall x, y | x in merged && y in left[i+1..]+right[j..] 
//                         ensures x <= y
//                     {
//                         if x in left[0..i+1] {
//                             assert x <= left[i];
//                             assert x <= y;
//                         }else{
//                             assert x in merged;
//                             assert x in right[0..j];
//                             var k :| 0 <= k < j <= |right| && x == right[k];
//                             assert k < j;
//                             if y in left[i+1..] {
//                                 assert y >= left[i]; 
//                                 if x == left[i] {
//                                     assert x <= left[i];
//                                 }else if x in oldmerged {
//                                     assert forall z, w :: z in oldmerged && w in left[i..]+right[j..] ==> z <= w; 
//                                     assert left[i] in left[i..]+right[j..];
//                                     assert x <= left[i];

//                                 }
//                                 assert x <= y;
//                             }else{
//                                 assert y in right[j..];
//                                 assert x <= y;

//                             }
//                         }
//                     }
//                 }
//                 // assert Sorted(merged) by {
//                 //     forall i,j | 0 <= i < j < |merged| 
//                 //         ensures merged[i] <= merged[j];
//                 //     {
                        
//                 //     }
//                 // }
//                 i := i + 1;
//             }else{
//                 assume forall x :: 0 <= x < |merged| ==> merged[x] <= right[j];
//                 assert right[0..j+1] == right[0..j] + [right[j]];
//                 merged := merged + [right[j]];
//                 assert forall x, y :: x in merged && y in left[i..]+right[j+1..] ==> x <= y;
//                 j := j + 1;
//                 assert Sorted(merged);
//                 inv := inv + |left| - i;
//             }
//             k := k + 1;

//             assume inv == |inversersionSetJoined(left[0..i], right[0..j])|;
//         }
//         assert i == |left|;
//         assert j == |right|;
//         assert left[0..i] == left;
//         assert right[0..j] == right;
//         assert multiset(left[0..i]) == multiset(left);
//         assert multiset(merged) == multiset(left + right);
//         return merged, inv;
//     }
}
