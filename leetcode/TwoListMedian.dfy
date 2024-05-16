module Median {
    predicate sortedRec(list: seq<int>) {
        if list == [] then true else (forall y :: y in list[1..] ==> list[0] <= y) && sortedRec(list[1..])
    }

    lemma sortedDefsAreEquivalent(list: seq<int>)
            ensures sortedRec(list) <==> Sorted(list)
        {
            if list == [] {}
            if sortedRec(list) == false && sortedRec(list[1..]) == false && forall y :: y in list[1..] ==> list[0] <= y {

            }else if sortedRec(list) == false && !(forall y :: y in list[1..] ==> list[0] <= y) && sortedRec(list[1..]) {
                assert exists x, k :: x in list[1..] && x < list[0] && 0 <= k < |list| && list[k] == x;
                assert !Sorted(list);
            }else if !Sorted(list) {
                if j, i :| 0 <= i < j < |list| && list[i] > list[j] {
                    var slice := list[i..];
                    assert list[j] in slice[1..];
                }
            }
        }

    function merge(xs: seq<int>, ys: seq<int>): seq<int>
        requires sortedRec(xs)
        requires sortedRec(ys)
        ensures sortedRec(merge(xs, ys))
        ensures multiset(merge(xs,ys)) == multiset(xs)+multiset(ys)
    {
        if xs == [] then ys else
        if ys == [] then xs else
        if xs[0] <= ys[0] then 
            assert xs == [xs[0]] + xs[1..];
            assert ys == [ys[0]] + ys[1..];
            assert forall x :: x in merge(xs[1..], ys) ==> x in xs[1..] || x in ys ==> xs[0] <= x;
            // assert sortedRec(merge(xs[1..], ys));
            var result := [xs[0]] + merge(xs[1..], ys);
            assert forall x :: x in result[1..] ==> x in multiset(xs[1..])+multiset(ys);
            result
        else 
            assert xs == [xs[0]] + xs[1..];
            assert ys == [ys[0]] + ys[1..];
            assert forall x :: x in merge(xs, ys[1..]) ==> x in xs || x in ys[1..] ==> ys[0] <= x;
            var result := [ys[0]] + merge(xs, ys[1..]);
            assert forall x :: x in result[1..] ==>x in multiset(xs) + multiset(ys[1..]);
            result
    }

    function {:verify true} merge_adj(xss: seq<seq<int>>): seq<seq<int>>
        requires forall xs :: xs in xss ==> sortedRec(xs)
        ensures |merge_adj(xss)| == (|xss| + 1)/2
        ensures mset_mset(xss) == mset_mset(merge_adj(xss))
        ensures forall xs :: xs in merge_adj(xss) ==> sortedRec(xs)
    {
    if xss == [] then []
    else if |xss| == 1 then xss
    else [merge(xss[0], xss[1])] + merge_adj(xss[2..])
    }

    function {:verify true} merge_all(xss: seq<seq<int>>): seq<int>
        requires forall xs :: xs in xss ==> sortedRec(xs)
        ensures sortedRec(merge_all(xss))
        ensures multiset(merge_all(xss)) == mset_mset(xss)
        decreases |xss|
    {
        if xss == [] then []
        else if |xss| == 1 then xss[0]
        else merge_all(merge_adj(xss))
    }


    function splitSeq(xs: seq<int>): seq<seq<int>>
        ensures multiset(xs) == mset_mset(splitSeq(xs))
        ensures forall ys :: ys in splitSeq(xs) ==> sortedRec(ys)
    {
        if xs == [] then [] else
            assert xs == [xs[0]] + xs[1..];
            [[xs[0]]] + splitSeq(xs[1..])
    }

    function {:verify true} msort_bu(xs: seq<int>): seq<int>
        ensures multiset(xs) == multiset(msort_bu(xs))
        ensures sortedRec(msort_bu(xs))
    {
        merge_all(splitSeq(xs))
    }

    function subtractOneFromList(xs: seq<int>, x: int): seq<int>
        requires x in multiset(xs)
    {
        if xs[0] == x then
            assert xs == [xs[0]] + xs[1..];
            assert multiset(xs) == multiset([xs[0]]) + multiset(xs[1..]);
            assert multiset(xs)-multiset{x} == multiset(xs[1..]);
            xs[1..]
        else
        [xs[0]] + subtractOneFromList(xs[1..], x)
    }

    function getIndex(xs: seq<int>, x: int): nat
        requires x in multiset(xs)
        ensures 0 <= getIndex(xs, x) < |xs|
        ensures xs[getIndex(xs, x)] == x
    {
        if xs[0] == x then 0 else 1 + getIndex(xs[1..], x)
    }

    lemma {:induction } {:timeLimit 30} subtractOneFromListIndex(xs: seq<int>, x: int)
        requires x in multiset(xs)
        ensures getIndex(xs, x) == 0 ==> subtractOneFromList(xs, x) == xs[1..]
        ensures getIndex(xs, x) != 0 ==> subtractOneFromList(xs, x) == xs[..getIndex(xs, x)] + xs[getIndex(xs, x)+1..]
    {
        assert xs[getIndex(xs, x)] == x;
        assert xs == xs[..getIndex(xs, x)] + [xs[getIndex(xs, x)]] + xs[getIndex(xs, x)+1..];
        // assert xs == xs[..getIndex(xs, x)] + [xs[getIndex(xs, x)]] + xs[getIndex(xs, x)+1..];
    }

    lemma subOneIndexLemma(xs: seq<int>, x: int)
        requires x in multiset(xs)
        ensures subtractOneFromList(xs, x) == xs[..getIndex(xs, x)] + xs[getIndex(xs, x)+1..]
    {
        subtractOneFromListIndex(xs, x);
        // assert xs == xs[..getIndex(xs, x)] + [xs[getIndex(xs, x)]] + xs[getIndex(xs, x)+1..];
    }

    lemma originalList(xs: seq<int>, x: int)
        requires x in multiset(xs)
        ensures xs == xs[..getIndex(xs, x)] + [xs[getIndex(xs, x)]] + xs[getIndex(xs, x)+1..]
    {
        assert xs == xs[..getIndex(xs, x)] + [xs[getIndex(xs, x)]] + xs[getIndex(xs, x)+1..];
    }

    lemma subOneSlices(xs: seq<int>, x: int)
        requires x in multiset(xs)
        ensures |subtractOneFromList(xs, x)| == |xs| - 1
        ensures subtractOneFromList(xs, x)[..getIndex(xs, x)] == xs[..getIndex(xs, x)]
        ensures subtractOneFromList(xs, x)[getIndex(xs, x)..] == xs[getIndex(xs, x)+1..]
    {
        // assert xs == xs[..getIndex(xs, x)] + [xs[getIndex(xs, x)]] + xs[getIndex(xs, x)+1..];
    }

    lemma subOneReconstruct(xs: seq<int>, x: int)
        requires x in multiset(xs)
        ensures |subtractOneFromList(xs, x)| == |xs| - 1
        ensures xs == subtractOneFromList(xs, x)[..getIndex(xs, x)] +[x]+subtractOneFromList(xs, x)[getIndex(xs, x)..]
    {
        subOneSlices(xs, x);
    }

    lemma subtractOneFromListLemma(xs: seq<int>, x: int)
        requires x in multiset(xs)
        ensures multiset(xs)-multiset{x} == multiset(subtractOneFromList(xs, x))
    {
        var retval := subtractOneFromList(xs, x);
        var mset := multiset(xs);
        if xs[0] == x {
            assert xs == [xs[0]] + xs[1..];
            assert mset == multiset([xs[0]]) + multiset(xs[1..]);
            assert mset - multiset{x} == multiset(xs[1..]);
            assert mset - multiset{x} == multiset(retval);
        } else {
            assert xs == [xs[0]] + xs[1..];
            assert mset == multiset([xs[0]]) + multiset(xs[1..]);
        }
    }

    lemma multisetsEqualSortedAreEqual(xs: seq<int>, ys: seq<int>)
        requires multiset(xs) == multiset(ys)
        requires sortedRec(xs)
        requires sortedRec(ys)
        ensures xs == ys
    {
        if xs == [] {
        } else {
            assert xs == [xs[0]] + xs[1..];
            assert ys == [ys[0]] + ys[1..];
            assert xs[0] == ys[0] by {
                assert xs[0] in multiset(xs) && xs[0] in multiset(ys) && xs[0] in ys;
                assert ys[0] in multiset(ys) && ys[0] in multiset(xs) && ys[0] in xs;
                if xs[0] != ys[0] {
                    if xs[0] < ys[0] {
                        assert xs[0] in ys[1..];
                        assert false;
                    } else {
                        assert xs[0] in ys[1..];
                        assert ys[0] in xs;
                        assert false;
                    }
                }
            }
            calc {
                multiset(xs[1..]);
                multiset(xs) - multiset{xs[0]};
                multiset(ys[1..]);
            }
            multisetsEqualSortedAreEqual(xs[1..], ys[1..]);
        }
    }

    lemma {:induction false} msorted_equal(xs: seq<int>, ys: seq<int>)
        requires sortedRec(xs)
        requires multiset(xs) == multiset(ys)
        decreases xs
        ensures xs == msort_bu(ys)
    {
        if xs == [] {
        } else {
            assert ys != [];
            assert xs == [xs[0]] + xs[1..];
            assert ys == [ys[0]] + ys[1..];
            assert xs[0] == msort_bu(ys)[0] by {
                assert xs[0] in multiset(xs) && xs[0] in multiset(ys) && xs[0] in msort_bu(ys);
                assert msort_bu(ys)[0] in multiset(msort_bu(ys)) && msort_bu(ys)[0] in multiset(ys) && msort_bu(ys)[0] in xs;
                if xs[0] != msort_bu(ys)[0] {
                    if xs[0] < msort_bu(ys)[0] {
                        assert xs[0] in msort_bu(ys)[1..];
                    } else {
                        assert msort_bu(ys)[0] in xs[1..];
                    }
                    assert false;
                }
            }
            var ys1: seq<int> := subtractOneFromList(ys, msort_bu(ys)[0]);
            subtractOneFromListLemma(ys, msort_bu(ys)[0]);
            calc {
                multiset(xs);
                multiset{msort_bu(ys)[0]} + multiset(xs[1..]);
            }
            assert msort_bu(ys) == [msort_bu(ys)[0]] + msort_bu(ys)[1..];
            calc {
                multiset(xs[1..]);
                multiset(ys1);
                {
                    assert multiset(msort_bu(ys)) - multiset{msort_bu(ys)[0]} == multiset(msort_bu(ys)[1..]);
                    assert multiset(ys) - multiset{msort_bu(ys)[0]} == multiset(msort_bu(ys)[1..]);
                    assert multiset(ys1) == multiset(ys) - multiset{msort_bu(ys)[0]};
                }
                multiset(msort_bu(ys)[1..]);
            }
            msorted_equal(xs[1..], ys1);
            assert xs[1..] == msort_bu(ys1);
            multisetsEqualSortedAreEqual(msort_bu(ys1), msort_bu(ys)[1..]);
            assert xs == msort_bu(ys);
        }
    }

    function mset_mset(xss: seq<seq<int>>): multiset<int>
        ensures forall xs :: xs in xss ==> forall x :: x in xs ==> x in mset_mset(xss) 
    {
        if xss == [] then multiset{} else
            assert xss == [xss[0]] + xss[1..]; 
            multiset(xss[0]) + mset_mset(xss[1..])
    }


    predicate Sorted(list: seq<int>) {
        forall i, j :: 0 <= i < j < |list| ==> list[i] <= list[j]
    }

    function median(list: seq<int>) : real 
        requires |list| > 0
        requires Sorted(list) || sortedRec(list)
    {
        if |list| % 2 == 0 then
            (list[|list| / 2 - 1] + list[|list| / 2]) as real / 2.0
        else
            list[|list| / 2] as real
    }

/*
    let n1 = nums1.length, n2 = nums2.length;
        
        // Ensure nums1 is the smaller array for simplicity
        if (n1 > n2) return findMedianSortedArrays(nums2, nums1);
        
        let n = n1 + n2;
        let left = (n1 + n2 + 1) / 2; // Calculate the left partition size
        let low = 0, high = n1;
        
        while (low <= high) {
            let mid1 = (low + high) >> 1; // Calculate mid index for nums1
            let mid2 = left - mid1; // Calculate mid index for nums2
            
            let l1 = -Infinity, l2 = -Infinity, r1 = Infinity, r2 = Infinity;
            
            // Determine values of l1, l2, r1, and r2
            if (mid1 < n1)
                r1 = nums1[mid1];
            if (mid2 < n2)
                r2 = nums2[mid2];
            if (mid1 - 1 >= 0)
                l1 = nums1[mid1 - 1];
            if (mid2 - 1 >= 0)
                l2 = nums2[mid2 - 1];
            
            if (l1 <= r2 && l2 <= r1) {
                // The partition is correct, we found the median
                if (n % 2 == 1)
                    return Math.max(l1, l2);
                else
                    return (Math.max(l1, l2) + Math.min(r1, r2)) / 2.0;
            }
            else if (l1 > r2) {
                // Move towards the left side of nums1
                high = mid1 - 1;
            }
            else {
                // Move towards the right side of nums1
                low = mid1 + 1;
            }
        }
        
        return 0; 
*/
    method TwoListMedian(list1: seq<int>, list2: seq<int>) returns (result: real)
        requires |list1| > 0
        requires |list2| > 0
        requires Sorted(list1)
        requires Sorted(list2)
        ensures result == median(msort_bu(list1 + list2))
    {
        return 0.0;
    }

    method TestMedian() {
        var list1 := [1, 3];
        var list2 := [2];
        var list3 := [4, 5];
        var result := median(msort_bu(list1 + list2));
        assert multiset(list1 + list2) == multiset(msort_bu(list1 + list2));
        assert multiset(msort_bu(list1 + list2)) == multiset([1, 2, 3]);
        assert multiset(list1)+multiset(list2) == multiset([1, 2, 3]);
        assert sortedRec([1, 2, 3]);
        msorted_equal([1, 2, 3], list1 + list2);
        assert msort_bu(list1 + list2) == [1, 2, 3];
        assert result == 2.0;
        assert median(list1 + list3) == 3.5;
    }
}