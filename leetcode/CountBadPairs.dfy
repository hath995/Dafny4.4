

include "../lib/sets.dfy"
module CountBadPairs {
    import opened SetCustom
    function AllPairs(nums: seq<int>): set<(nat, nat)>
    {
        set x, y | 0 <= x < |nums| && 0 <= y < |nums| && (x < y) :: (x,y)
    }

    function IncrementPairs(pairs: set<(nat, nat)>): set<(nat, nat)>
    {
        set pair | pair in pairs :: (pair.0+1,pair.1+1)
    }

    lemma IncrementPairsSize(pairs: set<(nat, nat)>)
        ensures |IncrementPairs(pairs)| == |pairs|
    {
        if pairs == {} {
            assert |pairs| == 0;
            assert IncrementPairs(pairs) == {};
            assert |IncrementPairs(pairs)| == 0;
        }else {
            var x :| x in pairs;
            IncrementPairsSize(pairs - {x});
            assert IncrementPairs(pairs) == IncrementPairs(pairs - {x}) + {(x.0+1,x.1+1)};
            assert |IncrementPairs(pairs)| == |pairs|;
        }
    }

    function ZeroPairs(length: nat): set<(nat, nat)>
    {
        set y:nat | 1 <= y <= length :: (0,y)
    }

    lemma ZeroPairsEqual(nums: seq<int>)
        requires |nums| > 0
        ensures ZeroPairs(|nums|-1) == set y:nat | 1 <= y < |nums| :: (0,y)
    {
    }

    lemma ZeroPairsSize(length: nat)
        ensures |ZeroPairs(length)| == length
    {
        if length == 0 {
            assert ZeroPairs(length) == {};

        }else if length == 1 {
            assert ZeroPairs(length) == {(0,1)};
            assert |ZeroPairs(length)| == 1;
            assert length == 1;

        }else {
            ZeroPairsSize(length-1);
            assert ZeroPairs(length) == ZeroPairs(length-1) + {(0,length)};
            assert |ZeroPairs(length)| == length;
        }
    }

    lemma AllPairsEqual(nums: seq<int>)
        requires |nums| > 0
        ensures AllPairs(nums) == ZeroPairs(|nums|-1) + IncrementPairs(AllPairs(nums[1..]))
    {
        if |nums| == 1 {
            assert nums == [nums[0]];
            assert AllPairs(nums) == {};
            assert ZeroPairs(|nums|-1) == {};
            assert IncrementPairs(AllPairs(nums[1..])) == {};
            assert AllPairs(nums) == ZeroPairs(|nums|-1) + IncrementPairs(AllPairs(nums[1..]));
        }else {
            assert nums == [nums[0]]+nums[1..];
            // AllPairsEqual(nums[1..]);
            forall p | p in AllPairs(nums)
                ensures p in ZeroPairs(|nums|-1) || p in IncrementPairs(AllPairs(nums[1..]))
            {
                if p.0 == 0 {
                    assert p in ZeroPairs(|nums|-1);
                }else {
                    assert p.0 > 0;
                    assert p.1 > p.0;
                    assert (p.0 - 1, p.1-1) in AllPairs(nums[1..]);
                    assert p in IncrementPairs(AllPairs(nums[1..]));
                }
            }
            assert AllPairs(nums) == ZeroPairs(|nums|-1) + IncrementPairs(AllPairs(nums[1..]));
        }
    }

    lemma GoodPairsLessThanAll(nums: seq<int>)
        requires |nums| > 0
        ensures GoodPairs(nums) <= AllPairs(nums)
    {

    }

    lemma SetSizes<T>(s1: set<T>, s2: set<T>)
        requires s1 <= s2
        ensures |s1| <= |s2|
    {
        if s1 == {} {
            assert |s1| == 0;
            assert |s2| >= 0;
        }else {
            var x :| x in s1;
            SetSizes(s1 - {x}, s2-{x});
        }
    }

    lemma GoodPairsSize(nums: seq<int>)
        requires |nums| > 0
        ensures |GoodPairs(nums)| <= |AllPairs(nums)|
    {
        GoodPairsLessThanAll(nums);
        SetSizes(GoodPairs(nums), AllPairs(nums));
    }

    lemma{:vcs_split_on_every_assert} AllPairsSize(nums: seq<int>)
        ensures |AllPairs(nums)| == |nums| * (|nums| - 1) / 2
    {
        if |nums| <= 1
        {
            assert |AllPairs(nums)| == 0;
            assert |nums| * (|nums| - 1) / 2 == 0;
        }
        else
        {
            assert nums == [nums[0]]+nums[1..];
            AllPairsSize(nums[1..]);
            AllPairsEqual(nums);
            IncrementPairsSize(AllPairs(nums[1..]));
            ZeroPairsSize(|nums|-1);
            assert ZeroPairs(|nums|-1) !! IncrementPairs(AllPairs(nums[1..]));
            assert AllPairs(nums) == ZeroPairs(|nums|-1) + IncrementPairs(AllPairs(nums[1..]));
            calc {
                |AllPairs(nums)|;
                |ZeroPairs(|nums|-1)| + |IncrementPairs(AllPairs(nums[1..]))|;
                |nums|-1 + |IncrementPairs(AllPairs(nums[1..]))|;
                |nums|-1 + (|nums|-1)*(|nums|-2)/2;
                |nums|-1 + (|nums|*|nums|-3*|nums|+2)/2;
                2*(|nums|-1)/2 + (|nums|*|nums|-3*|nums|+2)/2;
                (2*|nums|-2)/2 + (|nums|*|nums|-3*|nums|+2)/2;
                (2*|nums|-2 + |nums|*|nums|-3*|nums|+2)/2;
                (|nums|*|nums|-1*|nums|)/2;
                |nums|*(|nums|-1)/2;
                // |nums|-1 + (|nums|)*(|nums|-2)/2- (|nums|-2)/2;
            }
        }
    }

    function GoodPairs(nums: seq<int>): set<(nat, nat)>
    {
        set x, y | 0 <= x < |nums| && 0 <= y < |nums| && (x < y) && ((y-x) == (nums[y]-nums[x])) :: (x,y)
    }

    function GoodPairsI(nums: seq<int>, i: nat): set<(nat, nat)>
        requires i <= |nums|
    {
        set x, y | 0 <= x < i && 0 <= y < |nums| && (x < y) && ((y-x) == (nums[y]-nums[x])) :: (x,y)
    }

    function GoodPairsIK(nums: seq<int>, i: nat, k: nat): set<(nat, nat)>
        requires i < |nums|
        requires i < k <= |nums|
    {
        set y |  0 <= y < k && (i < y) && ((y-i) == (nums[y]-nums[i])) :: (i,y)
    }

    function GoodPairsII(nums: seq<int>, i: nat): set<(nat, nat)>
        requires i <= |nums|
    {
        set x, y | 0 <= x < i && 0 <= y < i && (x < y) && ((y-x) == (nums[y]-nums[x])) :: (x,y)
    }

    lemma GoodPairsIkNextPos(nums: seq<int>, i: nat, k: nat)
        requires i < |nums|
        requires i < k < |nums|
        requires nums[k] - nums[i] == k - i
        ensures GoodPairsIK(nums, i, k+1) == GoodPairsIK(nums, i, k) + {(i,k)}
    {
    }

    lemma GoodPairsIkNextNeg(nums: seq<int>, i: nat, k: nat)
        requires i < |nums|
        requires i < k < |nums|
        requires nums[k] - nums[i] != k - i
        ensures GoodPairsIK(nums, i, k+1) == GoodPairsIK(nums, i, k)
    {
    }

    lemma GoodPairsILessThanGoodPairs(nums: seq<int>, i: nat)
        requires i <= |nums|
        ensures GoodPairsI(nums, i) <= GoodPairs(nums)
    {
    }

    lemma GoodPairsInext(nums: seq<int>, i: nat)
        requires i < |nums|
        ensures GoodPairsI(nums, i+1) == GoodPairsI(nums, i) + GoodPairsIK(nums, i, |nums|)
    {
    }

    function BadPairs(nums: seq<int>): set<(nat, nat)>
    {
        // AllPairs(nums) - GoodPairs(nums)
        set x, y | 0 <= x < |nums| && 0 <= y < |nums| && (x < y) && ((y-x) != (nums[y]-nums[x])) :: (x,y)
    }

    lemma BadPairsEqualsAllMinusGood(nums: seq<int>)
        requires |nums| > 0
        ensures BadPairs(nums) == AllPairs(nums) - GoodPairs(nums)
    {
    }

    lemma BadPairsSize(nums: seq<int>)
        requires |nums| > 0
        ensures |BadPairs(nums)| == |AllPairs(nums)| - |GoodPairs(nums)|
    {
        BadPairsEqualsAllMinusGood(nums);
        // AllPairsSize(nums);
        // GoodPairsSize(nums);
        // SetSizes(BadPairs(nums), AllPairs(nums) - GoodPairs(nums));
    }


    /*
    let count = 0;
    function countBadPairs(nums: number[]): number {
        let count = 0;
        const n = nums.length;
        for(let i = 0; i < n-1; i++) {
            const iprime = nums[i]-i;
            for(let k = i + 1; k < n; k++) {
                // if(nums[k] - nums[i] == k-i) count++;
                if(nums[k] - k  == iprime) count++;
            }
        }

        return (n-1)*(n)/2-count
    };
    */
    method countBadPairs(nums: seq<int>) returns (count: nat)
        requires |nums| > 0
        ensures count == |BadPairs(nums)|
    {
        var goodCount := 0;
        ghost var pairsI: set<(nat, nat)> := {};
        for i := 0 to |nums|
            invariant 0 <= i <= |nums|
            invariant pairsI == GoodPairsI(nums, i)
            invariant goodCount == |GoodPairsI(nums, i)|
        {
            ghost var oldCount := goodCount;
            ghost var pairsIK: set<(nat, nat)> := {};
            for j :=  i + 1 to |nums|
                invariant i < j <= |nums|
                invariant pairsIK == GoodPairsIK(nums, i, j)
                invariant goodCount == oldCount + |pairsIK|
            {
                if nums[j] - nums[i] == j - i
                {
                    pairsIK := pairsIK + {(i,j)};
                    goodCount := goodCount + 1;
                    GoodPairsIkNextPos(nums, i, j);
                }else {
                    GoodPairsIkNextNeg(nums, i, j);
                }
            }
            // assert pairsIK == GoodPairsIK(nums, i, |nums|);
            pairsI := pairsI + pairsIK;
            GoodPairsInext(nums, i);
        }
        assert goodCount == |GoodPairsI(nums, |nums|)|;
        assert GoodPairsI(nums, |nums|) == GoodPairs(nums);
        // assert goodCount == |GoodPairs(nums)|;
        BadPairsSize(nums);
        GoodPairsSize(nums);
        AllPairsSize(nums);
        // assert |GoodPairs(nums)| <= |AllPairs(nums)|;

        return |nums| * (|nums| - 1) / 2 - goodCount;

    }

    lemma GoodPairAlt(nums: seq<int>, i: nat, k: nat)
        requires i < |nums|
        requires i < k < |nums|
        requires nums[k] - nums[i] == k - i
        ensures nums[k] - k == nums[i] - i
    {
    }

    lemma GoodPairAltAlt(nums: seq<int>, i: nat, k: nat)
        requires i < |nums|
        requires i < k < |nums|
        requires nums[k] - k == nums[i] - i
        ensures nums[k] - nums[i] == k - i
    {
    }

    function DiffsSet(nums: seq<int>): set<int>
    {
        set x | 0 <= x < |nums| :: nums[x] - x
    }

    lemma DiffsSetContains(nums: seq<int>, i: nat)
        requires i < |nums|
        requires nums[i] - i !in DiffsSet(nums[0..i])
        ensures DiffsSet(nums[0..i+1]) == DiffsSet(nums[0..i]) + {nums[i] - i}
    {
    }

    function IndicesCoset(nums: seq<int>, diff: int): set<nat>
        ensures forall i :: i in IndicesCoset(nums, diff) ==> 0 <= i < |nums|
    {
        set i | 0 <= i < |nums| && nums[i] - i == diff :: i
    }

    lemma lastIndices(nums: seq<int>, diff: int, i: nat)
        requires i < |nums|
        requires diff == nums[i] - i
        requires diff !in DiffsSet(nums[0..i])
        ensures IndicesCoset(nums[0..i+1], diff) == IndicesCoset(nums[0..i], diff) + {i}
    {
    }

    lemma nextIndices(nums: seq<int>, diff: int, i: nat)
        requires i < |nums|
        requires diff == nums[i] - i
        requires diff !in DiffsSet(nums[0..i])
        ensures forall xdiff :: xdiff in DiffsSet(nums[0..i]) ==> IndicesCoset(nums[0..i+1], xdiff) == IndicesCoset(nums[0..i], xdiff)
    {
        forall xdiff | xdiff in DiffsSet(nums[0..i])
            ensures IndicesCoset(nums[0..i+1], xdiff) == IndicesCoset(nums[0..i], xdiff)
        {
        }
    }

    lemma nextIndicesIn(nums: seq<int>, diff: int, i: nat)
        requires i < |nums|
        requires diff == nums[i] - i
        requires diff in DiffsSet(nums[0..i])
        ensures forall xdiff :: xdiff in DiffsSet(nums[0..i]) && xdiff != diff ==> IndicesCoset(nums[0..i+1], xdiff) == IndicesCoset(nums[0..i], xdiff)
    {
        forall xdiff | xdiff in DiffsSet(nums[0..i]) && xdiff != diff
            ensures IndicesCoset(nums[0..i+1], xdiff) == IndicesCoset(nums[0..i], xdiff)
        {
        }
    }


    lemma NotIndices(nums: seq<int>, diff: int, i: nat)
        requires i < |nums|
        requires diff == nums[i] - i
        requires diff !in DiffsSet(nums[0..i])
        ensures IndicesCoset(nums[0..i], diff) == {}
    {
    }
    
    lemma IndicesCosetElementsLessThanI(nums: seq<int>, i: int, diff: int)
        requires 0 <= i <= |nums|
        ensures forall x :: x in IndicesCoset(nums[0..i], diff) ==> 0 <= x < i
    {
    }

    ghost function IndicesCosets(nums: seq<int>, diff: set<int>): set<set<nat>>
        ensures forall x :: x in diff ==> IndicesCoset(nums, x) in IndicesCosets(nums, diff)
        ensures forall ics :: ics in IndicesCosets(nums, diff) ==> exists x :: x in diff && ics == IndicesCoset(nums, x)
    {
        if diff == {} then
            {}
        else 
            var x :| x in diff;
            // IndicesCosets(nums, diff - {x}) + {set i | 0 <= i < |nums| && nums[i] - i == x}
            IndicesCosets(nums, diff - {x}) + {IndicesCoset(nums, x)}
    }

    lemma IndicesCosetsContains(nums: seq<int>, diffs: set<int>, diff: int)
        requires diff in diffs
        ensures IndicesCosets(nums, diffs) == IndicesCosets(nums, diffs-{diff}) + {IndicesCoset(nums, diff)}
    {
    }

    function CosetToPairs(coset: set<nat>): set<(nat, nat)>
    {
        set x, y | x in coset && y in coset && x < y :: (x,y)
    }

    function CosetToPairInPlusOne(coset: set<nat>, nums: seq<int>, i: int): set<(nat, nat)>
        requires forall x :: x in coset ==> 0 <= x < i <= |nums|
        ensures forall p :: p in CosetToPairInPlusOne(coset, nums, i) ==> p.0 < p.1
    {
        set x | x in coset && x < i :: (x, i)
    }


    lemma CosetToPairPlusOne(coset: set<nat>, nums: seq<int>, i: int)
        requires forall x :: x in coset ==> 0 <= x < i < |nums|
        ensures |CosetToPairInPlusOne(coset, nums, i)| == |coset|
    {
        if coset == {} {
            assert |CosetToPairInPlusOne(coset, nums, i)| == 0;
        }else{
            var x :| x in coset;
            CosetToPairPlusOne(coset - {x}, nums, i);
            assert (x, i) !in CosetToPairInPlusOne(coset-{x}, nums, i);
            assert CosetToPairInPlusOne(coset, nums, i) == CosetToPairInPlusOne(coset-{x}, nums, i) + {(x, i)};
        }
    }

    lemma CosetToPairInSeq(coset: set<nat>, nums: seq<int>)
        requires forall i :: i in coset ==> 0 <= i < |nums|
        ensures forall p :: p in CosetToPairs(coset) ==> p.0 < p.1
        ensures forall p :: p in CosetToPairs(coset) ==> 0 <= p.0 < |nums|
        ensures forall p :: p in CosetToPairs(coset) ==> 0 <= p.1 < |nums|
    {
    }

    ghost function AllCosetPairs(cosets: set<set<nat>>): set<(nat, nat)>
        ensures forall x :: x in cosets ==> CosetToPairs(x) <= AllCosetPairs(cosets)
        ensures forall pairs :: pairs in AllCosetPairs(cosets) ==> exists x :: (x in cosets) && pairs in CosetToPairs(x)
    {
        if cosets == {} then
            {}
        else
            var x :| x in cosets;
            CosetToPairs(x) + AllCosetPairs(cosets - {x})
    }

    lemma AllCosetPairsPlusOne(cosets: set<set<nat>>, coset: set<nat>)
        requires coset !in cosets
        ensures AllCosetPairs(cosets + {coset}) == AllCosetPairs(cosets) + CosetToPairs(coset)
    {
    }

    lemma  AllCosetsPairsInNums(nums: seq<int>)
        requires |nums| > 0
        ensures forall p :: p in AllCosetPairs(IndicesCosets(nums, DiffsSet(nums))) ==> 0 <= p.0 < |nums| && 0 <= p.1 < |nums|
    {
      forall p | p in AllCosetPairs(IndicesCosets(nums, DiffsSet(nums)))
        ensures 0 <= p.0 < |nums| && 0 <= p.1 < |nums|
      {
        var cosets := IndicesCosets(nums, DiffsSet(nums));
        var coset :| coset in cosets && p in CosetToPairs(coset);
        CosetToPairInSeq(coset, nums);
      }
    }

    lemma AllCosetsEqualAllGoodPairs(nums: seq<int>)
        requires |nums| > 0
        ensures AllCosetPairs(IndicesCosets(nums, DiffsSet(nums))) == GoodPairs(nums)
    {

        forall p | p in GoodPairs(nums)
            ensures p in AllCosetPairs(IndicesCosets(nums, DiffsSet(nums)))
        {
            var i := p.0;
            var j := p.1;
            GoodPairAlt(nums, i, j);
            var diff := nums[i] - i;
            assert diff in DiffsSet(nums);
            var coset := IndicesCoset(nums, diff);
            assert i in coset;
            assert j in coset;
            assert coset in IndicesCosets(nums, DiffsSet(nums));
            assert i in coset;
            assert j in coset;

            assert p in CosetToPairs(coset);
            assert p in AllCosetPairs(IndicesCosets(nums, DiffsSet(nums)));
        }

        forall p | p in AllCosetPairs(IndicesCosets(nums, DiffsSet(nums)))
            ensures p in GoodPairs(nums)
        {
            var x :| x in IndicesCosets(nums, DiffsSet(nums)) && p in CosetToPairs(x);
            var diff :| diff in DiffsSet(nums) && x == IndicesCoset(nums, diff);
            assert p.0 < p.1;
            assert 0 <= p.0 < |nums|;
            // var diff := nums[p.0] - p.0;
            // assert diff in DiffsSet(nums);
        }
    }

    lemma IndicesCosetsContinuedNeg(nums: seq<int>, i: nat, diffCosets: map<int, set<nat>>, diffMap: map<int, nat>, diff: int)
        requires i < |nums|
        requires diff == nums[i] - i
        requires forall diff :: diff in DiffsSet(nums[..i]) ==> diff in diffMap
        requires forall diff :: diff in DiffsSet(nums[..i]) ==> diffMap[diff] == |IndicesCoset(nums[..i], diff)|
        requires forall diff :: diff in DiffsSet(nums[..i]) ==> diff in diffCosets
        requires forall diff :: diff in DiffsSet(nums[..i]) ==> diffCosets[diff] == IndicesCoset(nums[..i], diff)
        requires diff !in diffMap
        
        ensures forall ldiff :: ldiff in DiffsSet(nums[..i+1]) ==> ldiff in diffCosets[diff := {i}]
        ensures forall ldiff :: ldiff in DiffsSet(nums[..i+1]) ==> diffCosets[diff := {i}][ldiff] == IndicesCoset(nums[..i+1], ldiff)
        ensures forall ldiff :: ldiff in DiffsSet(nums[..i+1]) ==> ldiff in diffMap[diff := 1]
        ensures forall ldiff :: ldiff in DiffsSet(nums[..i+1]) ==> diffMap[diff := 1][ldiff] == |IndicesCoset(nums[..i+1], ldiff)|
    {
    }

    lemma  IndicesCosetsContinuedPos(nums: seq<int>, i: nat, diffCosets: map<int, set<nat>>, diffMap: map<int, nat>, diff: int)
        requires i < |nums|
        requires diff == nums[i] - i
        requires diff in DiffsSet(nums[..i])
        requires forall diff :: diff in DiffsSet(nums[..i]) ==> diff in diffMap
        requires forall diff :: diff in DiffsSet(nums[..i]) ==> diffMap[diff] == |IndicesCoset(nums[..i], diff)|
        requires forall diff :: diff in DiffsSet(nums[..i]) ==> diff in diffCosets
        requires forall diff :: diff in DiffsSet(nums[..i]) ==> diffCosets[diff] == IndicesCoset(nums[..i], diff)
        requires diff in diffMap
        requires diff in diffCosets
        
        ensures forall ldiff :: ldiff in DiffsSet(nums[..i+1]) ==> ldiff in diffCosets[diff := diffCosets[diff]+{i}]
        ensures forall ldiff :: ldiff in DiffsSet(nums[..i+1]) ==> diffCosets[diff := diffCosets[diff]+{i}][ldiff] == IndicesCoset(nums[..i+1], ldiff)
        ensures forall ldiff :: ldiff in DiffsSet(nums[..i+1]) ==> ldiff in diffMap[diff := diffMap[diff]+1]
        ensures forall ldiff :: ldiff in DiffsSet(nums[..i+1]) ==> diffMap[diff := diffMap[diff]+1][ldiff] == |IndicesCoset(nums[..i+1], ldiff)|
    {
        assert IndicesCoset(nums[..i+1], diff) == IndicesCoset(nums[..i], diff) + {i};
        assert forall ldiff :: ldiff in DiffsSet(nums[..i+1]) ==> diffCosets[diff := diffCosets[diff]+{i}][ldiff] == IndicesCoset(nums[..i+1], ldiff) by {
            forall ldiff | ldiff in DiffsSet(nums[..i+1])
                ensures diffCosets[diff := diffCosets[diff]+{i}][ldiff] == IndicesCoset(nums[..i+1], ldiff)
            {
                if ldiff == diff {
                    assert diff in DiffsSet(nums[..i]);
                    assert diffCosets[diff] == IndicesCoset(nums[..i], diff);
                    assert diffCosets[diff]+{i} == IndicesCoset(nums[..i], diff) + {i};
                    assert diffCosets[diff := diffCosets[diff]+{i}][ldiff] == IndicesCoset(nums[..i+1], ldiff);
                }else{
                    assert diffCosets[diff := diffCosets[diff]+{i}][ldiff] == IndicesCoset(nums[..i+1], ldiff);
                }
            }
        }
    }

    // function DiffSetPairs(nums: seq<int>): set<(nat, nat)>
    // {
    //     set x, y | 0 <= x < |nums| && x < y < |nums| && (nums[y] - y in DiffsSet(nums)) :: (x,y)
    // }

    // function DiffSetPartial(nums: seq<int>, i: nat, k: nat): set<(nat, nat)>
    //     requires i < |nums|
    //     requires i < k < |nums|
    // {
    //     set x | i < x < k && nums[x] - x == nums[i] - i :: (i,x)
    // }

    // function DiffIndexSetPartial(nums: seq<int>, i: nat, k: nat): set<nat>
    //     requires i < |nums|
    //     requires i < k < |nums|
    // {
    //     set x | i <= x < k && nums[x] - x == nums[i] - i :: x
    // }

    /*
    function countBadPairs(nums: number[]): number {
        let badCount = 0;
        let goodCount = 0;
        const n = nums.length;
        const diffMap: Map<number, number> = new Map();
        for(let i = 0; i < n; i++) {
            const diff = i-nums[i];
            let count = diffMap.get(diff) ?? 0;
            goodCount += count;
            //badCount += i-count;
            diffMap.set(diff, count+1);
        }
        return ((n-1)*n/2) - goodCount;
    };
    */

    lemma DiffMapKeysPos(nums: seq<int>, diffMap: map<int, nat>, i: nat)
        requires |nums| > 0
        requires i < |nums|
        requires diffMap.Keys == DiffsSet(nums[0..i])
        requires nums[i] - i in diffMap
        ensures diffMap[(nums[i] - i) := diffMap[nums[i] - i]+1].Keys == DiffsSet(nums[0..i+1])
    {
        var k :| k in diffMap.Keys && k == nums[i] - i;
        assert k in DiffsSet(nums[0..i]);
    }

    lemma DiffMapKeysNeg(nums: seq<int>, diffMap: map<int, nat>, i: nat)
        requires |nums| > 0
        requires i < |nums|
        requires diffMap.Keys == DiffsSet(nums[0..i])
        requires nums[i] - i !in diffMap
        ensures diffMap[(nums[i]-i) := 1].Keys == DiffsSet(nums[0..i+1])
    {}
    lemma {:isolate_assertions } diffCosetsValuesCont(nums: seq<int>, i: nat, diffCosets: map<int, set<nat>>, diff: int)
        requires i < |nums|
        requires diff == nums[i] - i
        requires diffCosets.Keys == DiffsSet(nums[0..i])
        requires diff in DiffsSet(nums[0..i])
        requires forall diff :: diff in DiffsSet(nums[0..i]) ==> diffCosets[diff] == IndicesCoset(nums[0..i], diff)
        requires diffCosets.Values == IndicesCosets(nums[0..i], DiffsSet(nums[0..i]))
        ensures diffCosets[diff := diffCosets[diff]+{i}].Values == IndicesCosets(nums[0..i+1], DiffsSet(nums[0..i+1]))
    {
        forall xdiff | xdiff in DiffsSet(nums[0..i+1])
            ensures diffCosets[diff := diffCosets[diff]+{i}][xdiff] == IndicesCoset(nums[0..i+1], xdiff)
        {
            nextIndicesIn(nums, diff, i);
            if xdiff == diff {
            }else{
            }
        }

        forall coset | coset in IndicesCosets(nums[0..i+1], DiffsSet(nums[0..i+1]))
            ensures coset in diffCosets[diff := diffCosets[diff]+{i}].Values
        {
        }

        forall val | val in diffCosets[diff := diffCosets[diff]+{i}].Values
            ensures val in IndicesCosets(nums[0..i+1], DiffsSet(nums[0..i+1]))
        {
            var key :| key in diffCosets[diff := diffCosets[diff]+{i}].Keys && val == diffCosets[diff := diffCosets[diff]+{i}][key];
            assert key in DiffsSet(nums[0..i+1]);
        }
    }

    lemma diffCosetsValuesNegCont(nums: seq<int>, i: nat, diffCosets: map<int, set<nat>>, diff: int)
        requires i < |nums|
        requires diff == nums[i] - i
        requires diffCosets.Keys == DiffsSet(nums[0..i])
        requires diff !in DiffsSet(nums[0..i])
        requires forall diff :: diff in DiffsSet(nums[0..i]) ==> diffCosets[diff] == IndicesCoset(nums[0..i], diff)
        requires diffCosets.Values == IndicesCosets(nums[0..i], DiffsSet(nums[0..i]))
        ensures diffCosets[diff := {i}].Values == IndicesCosets(nums[0..i+1], DiffsSet(nums[0..i+1]))
    {
        assert diff !in diffCosets.Keys;
        assert diffCosets.Keys < diffCosets[diff := {i}].Keys;
        assert {i} !in diffCosets.Values;
        assert diffCosets.Values < diffCosets[diff := {i}].Values;
        assert diffCosets.Values+{{i}} == diffCosets[diff := {i}].Values;
        IndicesCosetsNeg(nums, i, diff);
        assert IndicesCosets(nums[0..i+1], DiffsSet(nums[0..i+1])) == IndicesCosets(nums[0..i], DiffsSet(nums[0..i])) + {{i}};
    }

    lemma setsx<T>( x: T)
        ensures {} + {x} == {x}
    {
    }

    lemma {:isolate_assertions } IndicesCosetsNeg(nums: seq<int>, i: nat, diff: int)
        requires i < |nums|
        requires diff == nums[i] - i
        requires diff !in DiffsSet(nums[0..i])
        ensures IndicesCosets(nums[0..i+1], DiffsSet(nums[0..i+1])) == IndicesCosets(nums[0..i], DiffsSet(nums[0..i])) + {{i}};
    {
        assert {i} !in IndicesCosets(nums[0..i], DiffsSet(nums[0..i]));
        if i == 0 {
            assert DiffsSet(nums[0..i]) == {};
            assert IndicesCosets(nums[0..i], DiffsSet(nums[0..i])) == {};
            assert IndicesCoset(nums[0..i+1], diff) == {i};
            assert DiffsSet(nums[0..i+1]) == {diff};
            assert IndicesCosets(nums[0..i+1], DiffsSet(nums[0..i+1])) == IndicesCosets(nums[0..i], DiffsSet(nums[0..i])) + {{i}};
        }else{
            DiffsSetContains(nums, i);
            assert DiffsSet(nums[0..i+1]) == {diff} + DiffsSet(nums[0..i]);
            IndicesCosetsContains(nums[0..i+1], DiffsSet(nums[0..i+1]), diff);
            assert IndicesCosets(nums[0..i+1], DiffsSet(nums[0..i+1]))  == IndicesCosets(nums[0..i+1], DiffsSet(nums[0..i+1])-{diff}) + {IndicesCoset(nums[0..i+1], diff)};
            lastIndices(nums, diff, i);
            NotIndices(nums, diff, i);
            assert IndicesCoset(nums[0..i], diff) == {};
            assert IndicesCoset(nums[0..i+1], diff) == IndicesCoset(nums[0..i], diff) + {i};
            setsx(i);
            assert {} + {i} == {i};
            assert IndicesCoset(nums[0..i+1], diff) == {i};
            IndicesDiffsetMinusDiff(nums, i, diff);
            assert IndicesCosets(nums[0..i+1], DiffsSet(nums[0..i+1])-{diff}) == IndicesCosets(nums[0..i], DiffsSet(nums[0..i]));
            assert IndicesCosets(nums[0..i+1], DiffsSet(nums[0..i+1])) == IndicesCosets(nums[0..i], DiffsSet(nums[0..i])) + {{i}};
        }
    }

    lemma IndicesDiffsetMinusDiff(nums: seq<int>, i: nat, diff: int)
        requires i < |nums|
        requires diff == nums[i] - i
        requires diff !in DiffsSet(nums[0..i])
        ensures IndicesCosets(nums[0..i+1], DiffsSet(nums[0..i+1])-{diff}) == IndicesCosets(nums[0..i], DiffsSet(nums[0..i]))
    {
        DiffsSetContains(nums, i);
        assert DiffsSet(nums[0..i+1])-{diff} == DiffsSet(nums[0..i]);
        forall x | x in IndicesCosets(nums[0..i], DiffsSet(nums[0..i]))
            ensures x in IndicesCosets(nums[0..i+1], DiffsSet(nums[0..i]))
        {
            nextIndices(nums, diff, i);
        }

        forall x | x in IndicesCosets(nums[0..i+1], DiffsSet(nums[0..i]))
            ensures x in IndicesCosets(nums[0..i], DiffsSet(nums[0..i]))
        {
            nextIndices(nums, diff, i);
        }
        assert IndicesCosets(nums[0..i+1], DiffsSet(nums[0..i])) == IndicesCosets(nums[0..i], DiffsSet(nums[0..i]));
    }

    lemma {:verify false} goodPairsPosContinued(nums: seq<int>, i: nat, diffMap: map<int, nat>, diffCosets: map<int, set<nat>>, diff: int, goodPairs: set<(nat, nat)>)
        requires i < |nums|
        requires diff == nums[i] - i
        requires diff in diffMap
        requires diff in diffCosets
        requires diff in DiffsSet(nums[0..i])
        requires diffMap[diff] == |IndicesCoset(nums[0..i], diff)|
        requires diffCosets[diff] == IndicesCoset(nums[0..i], diff)
        requires goodPairs == AllCosetPairs(IndicesCosets(nums[0..i], DiffsSet(nums[0..i])))
        ensures goodPairs + CosetToPairInPlusOne(diffCosets[diff], nums, i) == AllCosetPairs(IndicesCosets(nums[0..i+1], DiffsSet(nums[0..i+1])))
    {}

    lemma {:verify false} IndicesCosetsCont(nums: seq<int>, i: nat, diff: int)
        requires |nums| > 0
        requires i < |nums|
        requires diff == nums[i] - i
        // requires diff !in DiffsSet(nums[0..i])
        ensures IndicesCosets(nums[0..i+1], DiffsSet(nums[0..i+1])) == IndicesCosets(nums[0..i], DiffsSet(nums[0..i])) + {IndicesCoset(nums[0..i+1], diff)}
        decreases i
    {
        if i == 0 {
            assert DiffsSet(nums[0..i]) == {};
            assert IndicesCosets(nums[0..i], DiffsSet(nums[0..i])) == {};
            assert nums[0..i+1] == [nums[0]];
            assert i < |nums[0..i+1]|;
            assert i in IndicesCoset(nums[0..i+1], diff);
            assert IndicesCosets(nums[0..1], DiffsSet(nums[0..1])) == IndicesCosets(nums[0..i], DiffsSet(nums[0..i])) + {IndicesCoset(nums[0..i+1], diff)};
        }else{
            // assert nums == nums[0..i]+nums[i..];
            // assert nums[0..i+1] == nums[0..i]+[nums[i]];
            // IndicesCosetsCont(nums, i-1, nums[i-1] - (i-1));
            if diff in DiffsSet(nums[0..i]) {
                assert IndicesCoset(nums[0..i+1], diff) == IndicesCoset(nums[0..i], diff) + {i};
            }else{
                assert IndicesCoset(nums[0..i+1], diff) == {i};
                assert IndicesCoset(nums[0..i], diff) == {};
                assert nums[0..i+1] == nums[0..i]+[nums[i]];
                assert {} in IndicesCosets(nums[0..i], DiffsSet(nums[0..i+1]));
                assert IndicesCosets(nums[0..i], DiffsSet(nums[0..i+1])) == IndicesCosets(nums[0..i], DiffsSet(nums[0..i]))+ {{}} by {
                    forall d | d in DiffsSet(nums[0..i+1])
                        ensures d != diff ==> IndicesCoset(nums[0..i], d) == IndicesCoset(nums[0..i+1], d)
                        ensures d == diff ==> IndicesCoset(nums[0..i], d) == {}
                    {
                        if d != diff {
                        forall index | index in IndicesCoset(nums[0..i], d)
                            ensures index in IndicesCoset(nums[0..i+1], d)
                        {
                            assert index < i;
                            assert index < i+1;
                            assert nums[0..i][index] == nums[0..i+1][index];
                            assert nums[0..i][index]-index == d;
                            assert nums[0..i+1][index]-index == d;
                            assert index in IndicesCoset(nums[0..i], d);
                            assert index in IndicesCoset(nums[0..i+1], d);
                        }

                        forall index | index in IndicesCoset(nums[0..i+1], d)
                            ensures index in IndicesCoset(nums[0..i], d)
                        {
                            assert index != i;
                            assert index < i;
                            assert index < i+1;
                            assert nums[0..i][index] == nums[0..i+1][index];
                            assert nums[0..i][index]-index == d;
                            assert nums[0..i+1][index]-index == d;
                            assert index in IndicesCoset(nums[0..i], d);
                        }
                        }else{

                        }
                    }

                    forall s | s in IndicesCosets(nums[0..i], DiffsSet(nums[0..i+1]))
                        ensures s in IndicesCosets(nums[0..i], DiffsSet(nums[0..i]))+{{}}
                    {
                       var y :| y in DiffsSet(nums[0..i+1]) && s == IndicesCoset(nums[0..i+1], y); 
                       if y != diff {
                           assert s == IndicesCoset(nums[0..i], y);
                           assert s in IndicesCosets(nums[0..i], DiffsSet(nums[0..i]));
                       }else{
                            assert s == {};
                            assert s in IndicesCosets(nums[0..i], DiffsSet(nums[0..i]))+{{}};
                       }
                    }

                    forall s | s in IndicesCosets(nums[0..i], DiffsSet(nums[0..i])) + {{}}
                        ensures s in IndicesCosets(nums[0..i+1], DiffsSet(nums[0..i+1]))
                    {
                    }
                }
                assert i < |nums[0..i+1]|;
                assert nums[i] == nums[0..i+1][i];
                assert diff in DiffsSet(nums[0..i+1]);
            }
            assert IndicesCosets(nums[0..i+1], DiffsSet(nums[0..i+1])) == IndicesCosets(nums[0..i], DiffsSet(nums[0..i])) + {IndicesCoset(nums[0..i+1], diff)};
        }
    }

    lemma {:verify false} goodPairsNegContinued(nums: seq<int>, i: nat, diffMap: map<int, nat>, diffCosets: map<int, set<nat>>, diff: int, goodPairs: set<(nat, nat)>)
        requires i < |nums|
        requires diff == nums[i] - i
        requires diff !in DiffsSet(nums[0..i])
        requires diff !in diffMap
        requires diff !in diffCosets
        // requires diffMap[diff] == |IndicesCoset(nums[0..i], diff)|
        // requires diffCosets[diff] == IndicesCoset(nums[0..i], diff)
        requires goodPairs == AllCosetPairs(IndicesCosets(nums[0..i], DiffsSet(nums[0..i])))
        ensures goodPairs == AllCosetPairs(IndicesCosets(nums[0..i+1], DiffsSet(nums[0..i+1])))
    {
        assert diff !in DiffsSet(nums[0..i]);
        assert forall k :: 0 <= k < i ==> (nums[k] - k) != diff; 
        assert diff in DiffsSet(nums[0..i+1]);
        var ics := IndicesCosets(nums[0..i+1], DiffsSet(nums[0..i+1]));
        var diffCoset :| diffCoset in ics && diffCoset == IndicesCoset(nums[0..i+1], diff);
        assert diffCoset == {i} by {
            assert nums == nums[0..i+1]+nums[i+1..];
            if diffCoset != {i} {
                assert i < |nums[0..i+1]|;
                assert nums[i] == nums[0..i+1][i];
                assert diff == nums[0..i+1][i] - i;
                assert i in diffCoset;
                assert diffCoset != {};
                if k :| k in diffCoset && k != i {
                    assert k < i;
                    assert nums[k] -k == diff;
                    assert false;
                }

                assert false;
            }
        }
        assert |diffCoset| == 1;
        assert CosetToPairs(diffCoset) == {};
        IndicesCosetsCont(nums, i, diff);
        assert IndicesCosets(nums[0..i+1], DiffsSet(nums[0..i+1])) == IndicesCosets(nums[0..i], DiffsSet(nums[0..i]))+{diffCoset};
        AllCosetPairsPlusOne(IndicesCosets(nums[0..i], DiffsSet(nums[0..i])), diffCoset);
        assert AllCosetPairs(IndicesCosets(nums[0..i], DiffsSet(nums[0..i]))) == AllCosetPairs(IndicesCosets(nums[0..i+1], DiffsSet(nums[0..i+1])));
    }


        /*
        essentially diff map is counting the number of indices that have the same difference
        between the value and the index. If the difference is the same for two indices, then
        there is a good pair. So we count the number of good pairs by adding the count of the
        difference in the map. If the difference is not in the map, then we add it to the map
        and also add the index to the diffIMap.
        
        so if indices t, x, y, z have the same difference, where t < x < y < z, then we have 6 good pairs
        (t,x), (t,y), (t,z),
        (x,y), (x,z), (y,z)

        if we find another index w with the same difference, then we have 4
        more good pairs (t,w), (x,w), (y,w), (z,w)

        */
    method countBadPairsFaster(nums: seq<int>) returns (count: nat)
        requires |nums| > 0
        ensures count == |BadPairs(nums)|
    {
        var badCount := 0;
        var goodCount := 0;
        var goodPairs: set<(nat, nat)> := {};
        var diffCosets: map<int, set<nat>> := map[];
        var diffCosetPairsMap: map<int, set<(nat, nat)>> := map[];
        var diffMap: map<int, nat> := map[];
        assert diffMap.Keys == {};
        for i := 0 to |nums|
            invariant 0 <= i <= |nums|
            // invariant forall k :: 0 <= k < i ==> nums[k] - k in diffMap
            invariant forall diff :: diff in  DiffsSet(nums[0..i]) ==> diff in diffMap.Keys

            invariant DiffsSet(nums[0..i]) == diffMap.Keys
            invariant diffCosets.Keys == diffMap.Keys

            //invariant forall diff :: diff in DiffsSet(nums[0..i]) ==> diff in diffCosetPairsMap
            invariant forall diff :: diff in DiffsSet(nums[0..i]) ==> diffCosets[diff] == IndicesCoset(nums[0..i], diff)
            invariant forall diff :: diff in DiffsSet(nums[0..i]) ==> diffMap[diff] == |IndicesCoset(nums[0..i], diff)|
            // invariant diffCosets.Values == IndicesCosets(nums[0..i], DiffsSet(nums[0..i]))
            invariant goodPairs == GoodPairsII(nums, i)
            invariant goodCount == |goodPairs|

            // invariant forall diff :: diff in diffMap ==> diffCosetPairsMap[diff] == CosetToPairs(diffCosets[diff])

            // invariant forall diff :: diff in diffIMap.Keys ==> 0 <= diffIMap[diff] < |nums| && (nums[diffIMap[diff]] - diffIMap[diff] == diff)
            // invariant forall diff :: diff in diffMap ==> diffMap[diff] == |GoodPairsIK(nums, diff + i)|
            // invariant goodCount == |GoodPairsII(nums, i)|
            // invariant badCount == |BadPairs(nums)|
        {
            var diff := nums[i]-i;
            print "goodPairs: ", goodPairs, "\n";
            print "goodPairsI", GoodPairsII(nums, i), "\n";
            if diff in diffMap {
                DiffMapKeysPos(nums, diffMap, i);
                // goodPairsPosContinued(nums, i, diffMap, diffCosets, diff, goodPairs);
                assert diff in DiffsSet(nums[0..i]);
                assert diff in diffCosets;
                IndicesCosetsContinuedPos(nums, i, diffCosets, diffMap, diff);
                var count := diffMap[diff];
                print "diffCosets[", diff, "]:before: ", diffCosets[diff], "\n";
                IndicesCosetElementsLessThanI(nums, i, diff);
                // diffCosetsValuesCont(nums, i, diffCosets, diff);
                GoodPairsIIPosContinued(nums, i, goodCount, diffMap, diffCosets, diff, goodPairs);
                print "diffCosets[", diff, "]:after: ", diffCosets[diff], "\n";
                // assert forall x :: x in diffCosets[diff] ==> 0 <= x <= i < |nums| by {
                //     assert diff in DiffsSet(nums[0..i]);
                //     assert diffCosets[diff] == IndicesCoset(nums[0..i], diff);
                //     forall x | x in diffCosets[diff]
                //         ensures 0 <= x <= i < |nums|
                //     {
                //         assert x in IndicesCoset(nums[0..i], diff);
                //     }
                // }
                var npair := CosetToPairInPlusOne(diffCosets[diff], nums, i);
                print "npair: ", npair, "\n";
                goodCount := goodCount + count;
                goodPairs := goodPairs + npair;
                diffMap := diffMap[diff := count + 1];
                diffCosets := diffCosets[diff := diffCosets[diff]+{i}];
                print "goodPairs:after: ", goodPairs, "\n";
                // diffCosetPairsMap := diffCosetPairsMap[diff := diffCosetPairsMap[diff] + CosetToPairInPlusOne(diffCosets[diff], nums, i)];
            }else{
                DiffMapKeysNeg(nums, diffMap, i);
                IndicesCosetsContinuedNeg(nums, i, diffCosets, diffMap, diff);
                // goodPairsNegContinued(nums, i, diffMap, diffCosets, diff, goodPairs);
                // diffCosetsValuesNegCont(nums, i, diffCosets, diff);
                goodPairsIINegContinued(nums, i, diffMap, diffCosets, diff, goodPairs);
                diffMap := diffMap[diff := 1];
                print "diffCosets[", diff, "]:before: {}\n";
                diffCosets := diffCosets[diff := {i}];
                print "diffCosets[", diff, "]:after: ", diffCosets[diff], "\n";
                assert CosetToPairs(diffCosets[diff]) == {};
                // diffCosetPairsMap := diffCosetPairsMap[diff := CosetToPairs(diffCosets[diff])];
            }
        }
        assert nums[..|nums|] == nums;
        assert GoodPairs(nums) == GoodPairsII(nums, |nums|);
        // assert diffCosets.Values == IndicesCosets(nums, DiffsSet(nums));
        // AllCosetsEqualAllGoodPairs(nums);
        // assert Union(diffCosetPairsMap.Values) == AllCosetPairs(IndicesCosets(nums, DiffsSet(nums)));
        assert goodCount == |GoodPairs(nums)|;
        BadPairsSize(nums);
        GoodPairsSize(nums);
        AllPairsSize(nums);
        return |nums| * (|nums| - 1) / 2 - goodCount;
    }

    lemma {:verify } goodPairsIINegContinued(nums: seq<int>, i: nat, diffMap: map<int, nat>, diffCosets: map<int, set<nat>>, diff: int, goodPairs: set<(nat, nat)>)
        requires i < |nums|
        requires diff == nums[i] - i
        requires diff !in DiffsSet(nums[0..i])
        requires diff !in diffMap
        requires diff !in diffCosets
        ensures GoodPairsII(nums, i) == GoodPairsII(nums, i+1)
    {
    }
    lemma {:verify } GoodPairsIIPosContinued(nums: seq<int>, i: nat, goodCount: nat, diffMap: map<int, nat>, diffCosets: map<int, set<nat>>, diff: int, goodPairs: set<(nat, nat)>)
        requires i < |nums|
        requires diff == nums[i] - i
        requires diff in DiffsSet(nums[0..i])
        requires diff in diffMap
        requires diff in diffCosets
        requires DiffsSet(nums[0..i]) == diffMap.Keys
        requires diffMap.Keys == diffCosets.Keys
        requires forall diff :: diff in DiffsSet(nums[0..i]) ==> diffCosets[diff] == IndicesCoset(nums[0..i], diff)
        requires forall diff :: diff in DiffsSet(nums[0..i]) ==> diffMap[diff] == |IndicesCoset(nums[0..i], diff)|
        requires goodCount == |GoodPairsII(nums, i)|
        requires forall x :: x in diffCosets[diff] ==> 0 <= x < i <= |nums|
        // ensures CosetToPairInPlusOne(diffCosets[diff], nums, i) == CosetToPairInPlusOne(diffCosets[diff], nums, i+1)
        ensures GoodPairsII(nums, i+1) == GoodPairsII(nums, i) + CosetToPairInPlusOne(diffCosets[diff], nums, i)
        ensures goodCount + diffMap[diff] == |GoodPairsII(nums, i+1)|
    {
        CosetToPairPlusOne(diffCosets[diff], nums, i);
        assert diffMap[diff] == |CosetToPairInPlusOne(diffCosets[diff], nums, i)|;
    }
    
    function {:isolate_assertions} CountBadPairsFasterRec(nums: seq<int>, i: int, goodCount: nat, diffCosets: map<int, set<nat>>, diffMap: map<int, nat>, goodPairs: set<(nat, nat)>) :nat
        decreases |nums| - i
        requires |nums| > 0
        requires 0 <= i <= |nums|
        requires DiffsSet(nums[0..i]) == diffMap.Keys
        requires diffMap.Keys == diffCosets.Keys
        requires forall diff :: diff in DiffsSet(nums[0..i]) ==> diffCosets[diff] == IndicesCoset(nums[0..i], diff)
        requires forall diff :: diff in DiffsSet(nums[0..i]) ==> diffMap[diff] == |IndicesCoset(nums[0..i], diff)|
        requires diffCosets.Values == IndicesCosets(nums[0..i], DiffsSet(nums[0..i]))
        requires goodPairs == GoodPairsII(nums, i)
        requires goodCount == |GoodPairsII(nums, i)|
        ensures i == |nums| ==> CountBadPairsFasterRec(nums, i, goodCount, diffCosets, diffMap, goodPairs) == |GoodPairsII(nums, i)|
    {
        if i == |nums| then 
            goodCount
        else
            var diff := nums[i] - i;
            if diff in diffMap then
                DiffMapKeysPos(nums, diffMap, i);
                diffCosetsValuesCont(nums, i, diffCosets, diff);
                IndicesCosetsContinuedPos(nums, i, diffCosets, diffMap, diff);
                var count := diffMap[diff];
                var npair := CosetToPairInPlusOne(diffCosets[diff], nums, i);
                IndicesCosetElementsLessThanI(nums, i, diff);
                GoodPairsIIPosContinued(nums, i, goodCount, diffMap, diffCosets, diff, goodPairs);
                CountBadPairsFasterRec(nums, i+1, goodCount+count, diffCosets[diff := diffCosets[diff] + {i}], diffMap[diff := count + 1], goodPairs + npair)
            else
                DiffMapKeysNeg(nums, diffMap, i);
                IndicesCosetsContinuedNeg(nums, i, diffCosets, diffMap, diff);
                diffCosetsValuesNegCont(nums, i, diffCosets, diff);
                goodPairsIINegContinued(nums, i, diffMap, diffCosets, diff, goodPairs);
                CountBadPairsFasterRec(nums, i+1, goodCount, diffCosets[diff := {i}], diffMap[diff := 1], goodPairs)
    }

    // lemma CountBadPairsRecCompletes(nums: seq<int>, i: nat, goodCount: nat, diffMap: map<int, nat>, diffCosets: map<int, set<nat>>, goodPairs: set<(nat, nat)>)
    //     requires |nums| > 0
    //     requires i < |nums|
    //     requires diffMap.Keys == DiffsSet(nums[0..i])
    //     requires diffCosets.Keys == DiffsSet(nums[0..i])
    //     requires forall diff :: diff in DiffsSet(nums[0..i]) ==> diffCosets[diff] == IndicesCoset(nums[0..i], diff)
    //     requires forall diff :: diff in DiffsSet(nums[0..i]) ==> diffMap[diff] == |IndicesCoset(nums[0..i], diff)|
    //     requires diffCosets.Values == IndicesCosets(nums[0..i], DiffsSet(nums[0..i]))
    //     requires goodPairs == GoodPairsII(nums, i)
    //     requires goodCount == |GoodPairsII(nums, i)|
    //     ensures CountBadPairsFasterRec(nums, i, goodCount, diffCosets, diffMap, goodPairs) == CountBadPairsFasterRec(nums, 0, 0, map[], map[], {})
    // {
    //     if i == |nums| {
    //     }else{
    //         var diff := nums[i] - i;
    //         if diff in diffMap {
    //             CountBadPairsRecCompletes(nums, i+1, goodCount+count, diffCosets[diff := diffCosets[diff] + {i}], diffMap[diff := count + 1], goodPairs + npair)
    //         }else{
    //             CountBadPairsRecCompletes(nums, i+1, goodCount, diffCosets[diff := {i}], diffMap[diff := 1], goodPairs)
    //         }
    //     }
    // }

    function CountBadPairsRec(nums: seq<int>): nat
        requires |nums| > 0
        ensures CountBadPairsRec(nums) == |BadPairs(nums)|
    {
        var goodCount := CountBadPairsFasterRec(nums, 0, 0, map[], map[], {});
        assume goodCount == |GoodPairs(nums)|;
        assert GoodPairs(nums) == GoodPairsII(nums, |nums|);
        BadPairsSize(nums);
        GoodPairsSize(nums);
        AllPairsSize(nums);
        |nums| * (|nums| - 1) / 2 - goodCount
    }
    
    method Main() {
        var result := countBadPairsFaster([4,1,3,3]);
        print "Result: ", result, "\n";
    }
}