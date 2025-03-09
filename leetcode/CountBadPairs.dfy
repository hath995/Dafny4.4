
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

    function DiffsSet(nums: seq<int>): set<int>
    {
        set x | 0 <= x < |nums| :: nums[x] - x
    }

    function IndicesCoset(nums: seq<int>, diff: int): set<nat>
        ensures forall i :: i in IndicesCoset(nums, diff) ==> 0 <= i < |nums|
    {
        set i | 0 <= i < |nums| && nums[i] - i == diff :: i
    }

    ghost function IndicesCosets(nums: seq<int>, diff: set<int>): set<set<nat>>
        ensures forall x :: x in diff ==> IndicesCoset(nums, x) in IndicesCosets(nums, diff)
    {
        if diff == {} then
            {}
        else 
            var x :| x in diff;
            // IndicesCosets(nums, diff - {x}) + {set i | 0 <= i < |nums| && nums[i] - i == x}
            IndicesCosets(nums, diff - {x}) + {IndicesCoset(nums, x)}
    }

    function CosetToPairs(coset: set<nat>): set<(nat, nat)>
    {
        set x, y | x in coset && y in coset && x < y :: (x,y)
    }

    ghost function AllCosetPairs(cosets: set<set<nat>>): set<(nat, nat)>
        ensures forall x :: x in cosets ==> CosetToPairs(x) <= AllCosetPairs(cosets)
    {
        if cosets == {} then
            {}
        else
            var x :| x in cosets;
            CosetToPairs(x) + AllCosetPairs(cosets - {x})
    }

    lemma AllCosetsEqualAllGoodPairs(nums: seq<int>)
        requires |nums| > 0
        ensures AllCosetPairs(IndicesCosets(nums, DiffsSet(nums))) == GoodPairs(nums)
    {
        // forall x | x in IndicesCosets(nums, DiffsSet(nums))
        //     ensures CosetToPairs(x) <= GoodPairs(nums)
        // {
        //     var i :| i in x;
        //     var j :| j in x;
        //     GoodPairAlt(nums, i, j);
        // }

        forall p | p in GoodPairs(nums)
            ensures p in AllCosetPairs(IndicesCosets(nums, DiffsSet(nums)))
        {
            var i := p.0;
            var j := p.1;
            GoodPairAlt(nums, i, j);
            var diff := nums[i] - i;
            assert diff in DiffsSet(nums);
            var coset := IndicesCoset(nums, diff);
            assert coset in IndicesCosets(nums, DiffsSet(nums));
            assert p in CosetToPairs(coset);
            assert p in AllCosetPairs(IndicesCosets(nums, DiffsSet(nums)));
        }

        forall p | p in AllCosetPairs(IndicesCosets(nums, DiffsSet(nums)))
            ensures p in GoodPairs(nums)
        {
            var diff := nums[p.0] - p.0;
            assert diff in DiffsSet(nums);
        }
    }

    function DiffSetPairs(nums: seq<int>): set<(nat, nat)>
    {
        set x, y | 0 <= x < |nums| && x < y < |nums| && (nums[y] - y in DiffsSet(nums)) :: (x,y)
    }

    function DiffSetPartial(nums: seq<int>, i: nat, k: nat): set<(nat, nat)>
        requires i < |nums|
        requires i < k < |nums|
    {
        set x | i < x < k && nums[x] - x == nums[i] - i :: (i,x)
    }

    function DiffIndexSetPartial(nums: seq<int>, i: nat, k: nat): set<nat>
        requires i < |nums|
        requires i < k < |nums|
    {
        set x | i <= x < k && nums[x] - x == nums[i] - i :: x
    }

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

    method countBadPairsFaster(nums: seq<int>) returns (count: nat)
        requires |nums| > 0
        ensures count == |BadPairs(nums)|
    {
        var badCount := 0;
        var goodCount := 0;
        ghost var diffIMap: map<int, nat> := map[];
        var diffMap: map<int, nat> := map[];
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
        for i := 0 to |nums|
            invariant 0 <= i <= |nums|
            invariant forall k :: 0 <= k < i ==> nums[k] - k in diffMap
            invariant forall diff :: diff in diffMap ==> diff in diffIMap
            invariant forall diff :: diff in diffIMap.Keys ==> 0 <= diffIMap[diff] < |nums| && (nums[diffIMap[diff]] - diffIMap[diff] == diff)
            // invariant forall diff :: diff in diffMap ==> diffMap[diff] == |GoodPairsIK(nums, diff + i)|
            //invariant goodCount == |GoodPairsI(nums, i)|
            // invariant badCount == |BadPairs(nums)|
        {
            var diff := nums[i]-i;
            if diff in diffMap {
                var count := diffMap[diff];
                goodCount := goodCount + count;
                diffMap := diffMap[diff := count + 1];
            }else{
                diffMap := diffMap[diff := 1];
                diffIMap := diffIMap[diff := i];
            }
        }
        assert goodCount == |GoodPairs(nums)|;
        BadPairsSize(nums);
        GoodPairsSize(nums);
        AllPairsSize(nums);
        return |nums| * (|nums| - 1) / 2 - goodCount;
    }
}