include "../lib/seq.dfy"
include "LongestPalindromSupp.dfy"
include "../lib/GenericMergeSort.dfy"
import opened Palindrome
import opened SeqCustom
import opened GenericMergeSort
import opened Std.Collections.Seq
/*
function toMultiset(s: string): Map<string, number> {
    const s_mset: Map<string, number> = new Map();
    for(let char of s) {
        if(s_mset.has(char)) {
            s_mset.set(char, s_mset.get(char)+1);
        }else{
            s_mset.set(char, 1);
        }
    }
    return s_mset;
}

function longestPalindrome(s: string): number {
    let smset = toMultiset(s);
    let length = 0;
    let odds = [];
    for(let count of smset.values()) {
        if(count % 2 == 0) {
            length += count;
        }else {
            odds.push(count);
        }
    }
    if(odds.length > 0) {
    odds.sort();
    length += odds.pop();
    length += odds.reduce((total, x) => total+x-1, 0);
    }

    return length;
}
*/

lemma allOnesDistinct<T>(ss: seq<T>) 
    requires forall key :: key in ss ==> multiset(ss)[key] == 1
    ensures distinct(ss)
{
    if |ss| > 0 {
        assert ss == [ss[0]] + ss[1..];
        assert distinct([ss[0]]);
        assert multiset(ss[1..]) == multiset(ss) - multiset{ss[0]};
        allOnesDistinct(ss[1..]);
    }
}

function SumMs(a: multiset<char>, b: multiset<char>): multiset<char> {
    a+b
}

method {:verify } {:vcs_split_on_every_assert} longestPalindrome(s: string) returns (length: int, ghost lpm: multiset<char>) 
    ensures |lpm| == length 
    // ensures lpm == largePalindromeMultiset(s)
    // ensures exists s': string :: multiset(s') == lpm && IsPalindrome(s')
    //ensures forall x :: x in allStrings(multiset(s)) ==> |s| <= |pt|
{
    reveal Map();
    reveal FoldRight();
    var smset := multiset(s);
    ghost var originalms := smset;
    ghost var oddPairs: seq<(int, char)> := [];
    var odds: seq<int> := [];
    length := 0;
    lpm := multiset{};

    ghost var removed: multiset<char> := multiset{};
    ghost var oddMset: multiset<char> := multiset{};
    ghost var ptMset: multiset<char> := multiset{};
    assert forall pair :: pair in oddPairs ==> pair.0 >= 0;
    assert  Map(joinPairs, oddPairs) ==[];
    assert FoldRight(SumMs, Map(joinPairs, oddPairs), multiset{}) == oddMset;
    while smset != multiset{} 
        invariant smset <= originalms
        invariant forall key :: key in smset ==> smset[key] == originalms[key];
        invariant smset !! ptMset
        invariant smset !! oddMset
        invariant ptMset !! oddMset
        invariant removed == ptMset + oddMset
        invariant originalms == smset + removed
        invariant forall key :: key in ptMset ==> charCountEven(key, ptMset) && originalms[key] == ptMset[key]
        invariant forall key :: key in oddMset ==> charCountOdd(key, oddMset) && originalms[key] == oddMset[key]
        invariant forall pair :: pair in oddPairs ==> pair.0 > 0
        invariant forall pair :: pair in oddPairs ==> pair.1 in oddMset && oddMset[pair.1] == pair.0
        invariant Map(pairSelect, oddPairs) == odds
        invariant FoldRight(SumMs,  Map(joinPairs, oddPairs), multiset{}) == oddMset
        invariant length == |ptMset|
    {

        var x :| x in smset;
        if smset[x] % 2 == 0 {
            length := length + smset[x];
            assert smset[x] == originalms[x];
            ptMset := ptMset[x := smset[x]];
        }else{
            odds := [smset[x]]+odds;
            ghost var what := (smset[x], x);
            assert smset[x] == originalms[x];
            MapMultisetConcat([(smset[x], x)], oddPairs, pairSecond);
            // assert multiset(Map(pairSecond, [what]+oddPairs)) ==  multiset(Map(pairSecond, [what]))+multiset(Map(pairSecond, oddPairs));
            // LemmaMapDistributesOverConcat(joinPairs,[(smset[x], x)], oddPairs);
            // assert Map(joinPairs, [(smset[x], x)]+ oddPairs) == [joinPairs((smset[x], x))]+Map(joinPairs, oddPairs);
            oddPairs := [(smset[x], x)]+oddPairs;
            oddMset := oddMset[x := smset[x]];            
        }
        removed := removed[x := smset[x]];
        smset := smset[x := 0];
    }
    assert forall key :: charCountEven(key, originalms) ==> key in ptMset && ptMset[key] == originalms[key];
    lpm := ptMset;
    if |odds| > 0 {
        var PairSort := new MergeSort(sortOnFirst);
        var IntSort := new MergeSort(gte);
        ghost var soddPairs := PairSort.mergesort(oddPairs);
        assert multiset(soddPairs) == multiset(oddPairs);
        var sodds := IntSort.mergesort(odds);
        SortedMapEqualsSorted(PairSort, IntSort,oddPairs, odds);
        // assert joinPairs(soddPairs[0]) <= oddMset;
            assert oddMset != multiset{};
            assert soddPairs[0] in soddPairs;
            assert soddPairs[0] in oddPairs;
            // assert soddPairs[0].1 in oddMset;
        // assert soddPairs[0].1 in largestOdd(originalms) by {
        // }

    }
}

method {:verify false} longestPalindromePartial(s: string) returns (length: int, odds: seq<nat>, ghost oddKey: seq<char>, ghost pt: string, ghost ptMset: multiset<char>, ghost oddMset: multiset<char>) 
    ensures IsPalindrome(pt)
    ensures |pt| % 2 == 0
    ensures |pt| == length
    ensures multiset(pt) == ptMset
    ensures multiset(s) == ptMset + oddMset
    ensures ptMset !! oddMset
    ensures ptMset <= multiset(s)
    ensures forall key :: key in ptMset ==> ptMset[key] % 2 == 0
    ensures forall key :: key in oddMset ==> oddMset[key] % 2 == 1
    ensures forall count :: count in odds ==> count > 0 && count % 2 == 1
    ensures |oddKey| == |odds|
    ensures distinct(oddKey)
    ensures forall key :: key in oddKey ==> key in oddMset
    ensures forall i :: 0 <= i < |odds| ==> oddMset[oddKey[i]] == odds[i]
{

    var mset := multiset(s);
    oddKey := [];
    odds := [];
    length := 0;

    pt := "";
    ghost var removed: multiset<char> := multiset{};
    oddMset := multiset{};
    ptMset := multiset{};
    while mset != multiset{}
        invariant IsPalindrome(pt)
        invariant forall key :: key in ptMset ==> ptMset[key] % 2 == 0
        invariant forall key :: key in oddMset ==> oddMset[key] % 2 == 1
        invariant forall count :: count in odds ==> count > 0 && count % 2 == 1
        // invariant mset !! removed
        invariant mset !! ptMset
        invariant mset !! oddMset
        invariant ptMset !! oddMset
        invariant multiset(s) == mset + removed
        invariant removed == ptMset + oddMset
        invariant multiset(s) == ptMset + oddMset + mset 
        invariant |pt| == length
        invariant |pt| % 2 == 0
        invariant multiset(pt) == ptMset
        invariant |oddKey| == |odds|
        invariant forall key :: key in oddKey ==> multiset(oddKey)[key] == 1
        // invariant distinct(oddKey)
        invariant forall key :: key in oddKey ==> key in oddMset
        invariant forall i :: 0 <= i < |odds| ==> oddMset[oddKey[i]] == odds[i]
        // invariant multiset(pt) == ptMset
    {
        var x :| x in mset;
        if mset[x] % 2 == 0 {
            length := length + mset[x];
            ghost var repchar := rep(x, mset[x]/2);
            assert multiset(repchar)[x] == mset[x]/2;
            PalindromePlusRep(pt, x, mset[x]/2);
            calc {
                multiset(repchar+repchar)+multiset(pt);
                multiset(repchar+pt+repchar);
            }
            assert multiset(repchar+repchar)[x] == mset[x];
            assert multiset(repchar+repchar)+multiset(pt) == ptMset[x := mset[x]];
            pt := repchar+pt+repchar;
            ptMset := ptMset[x := mset[x]];
        }else{
            oddKey := oddKey + [x];
            odds := odds + [mset[x]];
            oddMset := oddMset[x := mset[x]];            
            assert odds[|odds|-1] == oddMset[x];
        }
        removed := removed[x := mset[x]];
        mset := mset[x := 0];
    }
    allOnesDistinct(oddKey);
}

// method {:verify false} longestPalindromePieces(s: string) returns (length: int, ghost pt: string, ghost ptmset: multiset<char>) 
//     ensures |pt| == length 
//     ensures IsPalindrome(pt)
//     ensures multiset(pt) <= multiset(s) 
//     ensures multiset(pt) == ptmset
//     // ensures largePalindromeMultiset(s) == ptmset
//     //ensures forall x :: x in allStrings(multiset(s)) ==> |s| <= |pt|
// {
//     var plength, odds, oddKey, ppt, ptMset, oddMset := longestPalindromePartial(s);
//     ptmset := ptMset;
//     length := plength;
//     pt := ppt;
//     var sodds := isort(odds);
//     assert multiset(odds) == multiset(sodds);
//     assert |odds| == |sodds|;
//     isortProperties(odds);
//     // assert ptMset + multiset(sodds) == multiset(s);

//     assert forall count :: count in sodds ==> count in odds;
//     assert forall count :: count in sodds ==> count > 0 && count % 2 == 1;

//     if |sodds| > 0 {
//         assert sodds[0] in sodds;
//         // assert sodds[0] in odds;
//         PalindromePlusRepOdd(pt, oddKey[0], sodds[0]);
//         assert pt == pt[0..|pt|/2] + pt[|pt|/2..];
//         pt := pt[0..|pt|/2]+rep(oddKey[0], sodds[0])+pt[|pt|/2..];
//         assert IsPalindrome(pt);
//         length := length + sodds[0];
//         assert forall i :: 1 <= i < |oddKey| ==> oddKey[i] !in ptMset;

//         ptMset := ptMset[oddKey[0] := sodds[0]];
//         ptmset := ptmset[oddKey[0] := sodds[0]];
//         assert ptMset == multiset(pt);
//         assert ptmset == multiset(pt);
//         assert ptmset <= multiset(s);
//         assert length == |pt|;
//         // assert forall count :: count in odds ==> count > 0 && count % 2 == 1;
//         // assert odds == [odds[0]]+odds[1..];
//         assert forall count :: count in odds[1..] ==> count > 0 && count % 2 == 1 by {
//             forall count | count in odds[1..] 
//                 ensures count in odds
//             {
//                 assert count in odds;
//             }
//         }
//         odds := odds[1..];
//         // assert forall count :: count in odds ==> count > 0 && count % 2 == 1;
//         // for i := 0 to |odds| 
//         //     invariant forall count :: count in odds ==> count > 0 && count % 2 == 1
//         //     invariant IsPalindrome(pt)
//         //     invariant length == |pt|

//         //     invariant forall k :: i < k < |oddKey| ==> oddKey[k] !in ptMset
//         //     invariant ptMset == multiset(pt)
//         //     invariant ptmset == multiset(pt)
//         //     invariant ptMset <= multiset(s)
//         // {
//         //     assert odds[i] in odds; 
//         //     ghost var repchar := rep(oddKey[i+1], (odds[i]-1)/2);

//         //     calc {
//         //         multiset(repchar+repchar)+multiset(pt);
//         //         multiset(repchar+pt+repchar);
//         //     }
//         //     assert multiset(repchar+repchar)[oddKey[i+1]] == odds[i]-1;
//         //     // assume oddKey[i+1] !in ptMset;
//         //     assert multiset(repchar+repchar)+multiset(pt) == ptMset[oddKey[i+1] := odds[i]-1];
//         //     PalindromePlusRep(pt, oddKey[i+1], (odds[i]-1)/2);
//         //     pt := repchar+pt+repchar;
//         //     length := length + odds[i] - 1;
//         //     ptMset := ptMset[oddKey[i+1] := odds[i]-1];
//         //     ptmset := ptmset[oddKey[i+1] := odds[i]-1];
//         // }
//     }
// }

method {:verify false } longestPalindromeOrig(s: string) returns (length: int, ghost pt: string) 
    ensures |pt| == length 
    ensures IsPalindrome(pt)
    ensures multiset(pt) <= multiset(s) 
    //ensures forall x :: x in allStrings(multiset(s)) ==> |s| <= |pt|
{
    var mset := multiset(s);
    ghost var oddKey: seq<char> := [];
    var odds: seq<nat> := [];
    length := 0;

    pt := "";
    ghost var removed: multiset<char> := multiset{};
    ghost var oddMset: multiset<char> := multiset{};
    ghost var ptMset: multiset<char> := multiset{};
    while mset != multiset{}
        invariant IsPalindrome(pt)
        invariant forall key :: key in ptMset ==> ptMset[key] % 2 == 0
        invariant forall key :: key in oddMset ==> oddMset[key] % 2 == 1
        invariant forall count :: count in odds ==> count > 0 && count % 2 == 1
        // invariant mset !! removed
        invariant mset !! ptMset
        invariant mset !! oddMset
        // invariant ptMset !! oddMset
        invariant multiset(s) == mset + removed
        invariant removed == ptMset + oddMset
        invariant multiset(s) == ptMset + oddMset + mset 
        invariant |pt| == length
        invariant |pt| % 2 == 0
        invariant multiset(pt) == ptMset
        invariant |oddKey| == |odds|
        invariant forall key :: key in oddKey ==> key in oddMset
        invariant forall i :: 0 <= i < |odds| ==> oddMset[oddKey[i]] == odds[i]
        // invariant multiset(pt) == ptMset
    {
        var x :| x in mset;
        if mset[x] % 2 == 0 {
            length := length + mset[x];
            ghost var repchar := rep(x, mset[x]/2);
            assert multiset(repchar)[x] == mset[x]/2;
            PalindromePlusRep(pt, x, mset[x]/2);
            calc {
                multiset(repchar+repchar)+multiset(pt);
                multiset(repchar+pt+repchar);
            }
            assert multiset(repchar+repchar)[x] == mset[x];
            assert multiset(repchar+repchar)+multiset(pt) == ptMset[x := mset[x]];
            pt := repchar+pt+repchar;
            ptMset := ptMset[x := mset[x]];
        }else{
            oddKey := oddKey + [x];
            odds := odds + [mset[x]];
            oddMset := oddMset[x := mset[x]];            
            assert odds[|odds|-1] == oddMset[x];
        }
        removed := removed[x := mset[x]];
        mset := mset[x := 0];
    }
    if |odds| > 0 {
        assert odds[0] in odds;
        PalindromePlusRepOdd(pt, oddKey[0], odds[0]);
        pt := pt[0..|pt|/2]+rep(oddKey[0], odds[0])+pt[|pt|/2..];
        assert IsPalindrome(pt);
        length := length + odds[0];
        assert length == |pt|;
        // assert forall count :: count in odds ==> count > 0 && count % 2 == 1;
        // assert odds == [odds[0]]+odds[1..];
        assert forall count :: count in odds[1..] ==> count > 0 && count % 2 == 1 by {
            forall count | count in odds[1..] 
                ensures count in odds
            {
                assert count in odds;
            }
        }
        odds := odds[1..];
        // assert forall count :: count in odds ==> count > 0 && count % 2 == 1;
        for i := 0 to |odds| 
            invariant forall count :: count in odds ==> count > 0 && count % 2 == 1
            invariant IsPalindrome(pt)
            invariant length == |pt|
        {
            assert odds[i] in odds; 
            ghost var repchar := rep(oddKey[i+1], (odds[i]-1)/2);
            PalindromePlusRep(pt, oddKey[i+1], (odds[i]-1)/2);
            pt := repchar+pt+repchar;
            length := length + odds[i] - 1;
        }
    }

}