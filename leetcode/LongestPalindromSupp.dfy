
include "../lib/seq.dfy"
module Palindrome {
    import opened SeqCustom

    ghost function allPermutations(str: string): iset<string> {
        iset ss: string | multiset(ss) == multiset(str)
    }

    lemma allPermutationsSameLength(str: string)
        ensures forall ss :: ss in allPermutations(str) ==> |ss| == |str|
    {
        forall ss | ss in allPermutations(str)
            ensures |ss| == |str|
        {
            assert multiset(ss) == multiset(str);
        }
    }

    lemma allPermutationsSameLengthOrLess(str: string)
        ensures forall ss :: ss in allSubStrings(str) ==> |ss| <= |str|
    {
        forall ss | ss in allSubStrings(str) 
            ensures |ss| <= |str|
        {
            if multiset(ss) == multiset(str) {
                allPermutationsSameLength(str);
            }else {
                assert multiset(ss) < multiset(str);
                multisetSubsetSmaller(multiset(str), multiset(ss));
            }
        }
    }

    ghost function allSubStrings(str: string): iset<string> {
        iset ss: string | multiset(ss) <= multiset(str)
    }

    ghost function allPalindromSubStrings(str: string): iset<string> {
        iset ss: string | multiset(ss) <= multiset(str) && IsPalindrome(ss)
    }

    ghost function allStrings(ms: multiset<char>): iset<string> {
        iset ss: string | multiset(ss) <= ms
    }

    ghost function allPalindromeStrings(ms: multiset<char>): iset<string> {
        iset ss: string | multiset(ss) <= ms && IsPalindrome(ss)
    }

    predicate IsPalindrome(s: string) {
        s == reverse(s)
    }

    predicate IsPalindromeK(s: string) {
        forall i :: 0 <= i < |s| ==> s[i] == s[|s|-i-1]
    }

    lemma PalindromeLeft(s: string)
        requires IsPalindrome(s)
        ensures IsPalindromeK(s)
    {
        ReverseIndexAll(s);
    }

    lemma PalindromeRight(s: string)
        requires IsPalindromeK(s)
        ensures IsPalindrome(s)
    {
        ReverseIndexAll(s);
    }

    lemma PalindromeSlicesPalindrome(s: string, i: int)
        requires IsPalindrome(s)
        requires |s| >= 2
        requires 0 <= i < |s|/2
        ensures IsPalindrome(s[(i+1)..(|s|-i-1)])
    {
        PalindromeLeft(s);
        PalindromeRight(s[(i+1)..(|s|-i-1)]);
    }

    lemma PalindromeSubstring(s: string)
        requires |s| > 1
        requires IsPalindrome(s)
        ensures IsPalindrome(s[1..|s|-1])
    {
        PalindromeLeft(s);
        assert s == [s[0]]+s[1..|s|-1]+[s[|s|-1]];
        var next := s[1..|s|-1];
        forall k | 0 <= k < |next| 
            ensures next[k] == next[|next|-k-1]
        {

        }
        PalindromeRight(next);
    }

    function rep(c: char, count: nat): string 
        ensures |rep(c, count)| == count
        ensures forall i :: 0 <= i < count ==> rep(c, count)[i] == c
        ensures multiset(rep(c, count))[c] == count
    {
        if count == 0 then "" else [c]+rep(c, count - 1)
    }

    lemma PalindromePlus(s: string, c: char) 
        requires IsPalindrome(s)
        ensures IsPalindrome([c]+s+[c])
    {
        ReverseIndexAll(s);
        ReverseIndexAll([c]+s+[c]);
    }

    lemma PalindromePlusRep(s: string, c: char, count: nat) 
        requires IsPalindrome(s)
        ensures IsPalindrome(rep(c, count)+s+rep(c, count))
    {
        ReverseIndexAll(s);
        ReverseIndexAll(rep(c, count)+s+rep(c, count));
    }

    lemma PalindromePlusRepOdd(s: string, c: char, count: nat) 
        requires count > 0 && count % 2 == 1
        requires IsPalindrome(s)
        requires |s| % 2 == 0
        ensures IsPalindrome(s[0..|s|/2]+rep(c, count)+s[|s|/2..])
    {
        ReverseIndexAll(s);
        ReverseIndexAll(s[0..|s|/2]+rep(c, count)+s[|s|/2..]);
    }
    lemma MinimumIndexExists(s: string, c: char) returns (i: int)
        requires c in s
        requires multiset(s)[c] > 0
        ensures  0 <= i < |s| && s[i] == c && forall k :: 0 <= k < |s| && s[k] == c ==> i <= k 
    {
        var k :| 0 <= k < |s| && s[k] == c;
        if c in s[..k] {
            i := MinimumIndexExists(s[..k],c);
        }else{
            i := k;
        }
    }

    function countChar(s: string, c: char): nat {
        if s == "" then 0 else if s[0] == c then 1 + countChar(s[1..], c) else countChar(s[1..], c)
    }

    lemma countCharEqualMultiplicity(s: string, c: char) 
        ensures countChar(s, c) == multiset(s)[c]
    {
        if s == "" {} else {
            assert s == [s[0]]+s[1..];
        }
    }

    predicate IsPalindrome2(s: string)
    {
        if |s|%2==0 then multiset(s[..|s|/2]) == multiset(s[|s|/2..]) else multiset(s[..|s|/2]) == multiset(s[(|s|/2+1)..])
    }

    lemma ip2(s: string)
        requires IsPalindrome(s)
        ensures IsPalindrome2(s)
    {
        PalindromeLeft(s);
        assert forall i :: 0 <= i < |s|/2 ==> s[i] == s[|s|-i-1];
        if |s| > 1 {
            PalindromeSubstring(s);
            if |s| % 2 == 0 {
            assert s == [s[0]]+s[1..|s|/2]+s[|s|/2..|s|-1]+[s[|s|-1]];
            assert s[..|s|/2] == [s[0]]+s[1..|s|/2];
            assert s[|s|/2..] == s[|s|/2..|s|-1]+[s[|s|-1]];

            assert s[1..|s|/2]+s[|s|/2..|s|-1] ==s[1..|s|-1]; 
            assert IsPalindrome(s[1..|s|/2]+s[|s|/2..|s|-1]);
            ip2(s[1..|s|-1]);
            var next := s[1..|s|-1];
            assert multiset(next[..|next|/2]) == multiset(next[|next|/2..]);
            assert next[..|next|/2] == s[1..|s|/2];
            assert next[|next|/2..] == s[|s|/2..|s|-1];
            assert multiset([s[0]]) == multiset([s[|s|-1]]);
            assert multiset([s[0]]) + multiset(next[..|next|/2]) == multiset(next[|next|/2..])+multiset([s[|s|-1]]);
            }else{
            assert s == [s[0]]+s[1..|s|/2]+[s[|s|/2]]+s[(|s|/2+1)..|s|-1]+[s[|s|-1]];
            assert s[..|s|/2] == [s[0]]+s[1..|s|/2];
            assert s[(|s|/2+1)..] == s[(|s|/2+1)..|s|-1]+[s[|s|-1]];
            assert s[1..|s|/2]+[s[|s|/2]]+s[(|s|/2+1)..|s|-1] ==s[1..|s|-1]; 
            assert IsPalindrome(s[1..|s|-1]);
            ip2(s[1..|s|-1]);
            var next := s[1..|s|-1];
            assert multiset(next[..|next|/2]) == multiset(next[(|next|/2+1)..]);
            assert next[..|next|/2] == s[1..|s|/2];
            assert next[(|next|/2+1)..] == s[(|s|/2+1)..|s|-1];
            }
        }else{
            assert |s| <= 1;
        }
    }
    

    lemma msLength(s: string) 
        ensures |s| == |multiset(s)|
    {}

    lemma multSize<T(==)>(ms: multiset<T>, x: T)
        requires |ms| > 0 
        requires x in ms
        ensures |ms| >= ms[x] >= 1
    {

    }

    lemma multisetSubsetSmaller<T(==)>(ms: multiset<T>, mss: multiset<T>)
        requires |ms| > 0
        requires mss < ms
        ensures |mss| < |ms|
    {
        if |ms| == 1 {
            var x :| x in ms;
            assert ms[x] == 1;
            assert |multiset{x}| == 1;
            assert |ms-multiset{x}| == 0;
            assert ms-multiset{x} == multiset{};
            assert ms == multiset{x};
            assert mss[x] < 1;
            assert mss == multiset{};
        }else{
            var x :| x in ms;
            var stub : multiset<T> := multiset{};
            if mss[x] == ms[x] {
                multisetSubsetSmaller(ms[x:=0], mss[x:=0]);
            }else if mss[x] < ms[x] {
                if mss[x:=0] < ms[x:=0] {
                    multisetSubsetSmaller(ms[x:=0], mss[x:=0]);
                } else if mss[x:=0] == ms[x:=0] {
                    assert mss == mss[x:=0] +stub[x:=mss[x]];
                    assert |mss| < |ms|;
                }else{

                }
            }
        }
    }

    lemma multisetSubsetSmallerEqual<T(==)>(ms: multiset<T>, mss: multiset<T>)
        requires mss <= ms
        ensures |mss| <= |ms|
    {
        if |ms| == 0 {

        }else{
            var x :| x in ms;
            if mss[x] == ms[x] {
                multisetSubsetSmallerEqual(ms[x:=0], mss[x:=0]);
            }else if mss[x] < ms[x] {
                if mss[x:=0] < ms[x:=0] {
                    multisetSubsetSmallerEqual(ms[x:=0], mss[x:=0]);
                }else{
                    assert mss[x:=0] == ms[x:=0];
                    assert |mss[x:=0]| == |ms[x:=0]|;
                    assert |mss| < |ms|;

                }
            }
        }
    }

    lemma allSubmultisetsShorter(s: string, mss: multiset<char>)
        requires |s| > 0
        requires mss < multiset(s)
        ensures forall xx :: xx in allStrings(mss) ==> |xx| < |s|
    {
        msLength(s);
        var ms := multiset(s);
        assert |ms| == |s|;
        multisetSubsetSmaller(ms, mss);
        assert |mss| < |ms|;
        forall xx | xx in allStrings(mss)
            ensures |xx| < |s|
        {
                multisetSubsetSmaller(ms, multiset(xx));
        }
    }

    method Test() {
        var example := "abcqqqcba";
        assert IsPalindrome(example);
        var ms:= multiset(example);
        assert example in allPalindromeStrings(ms);
    }
    
    lemma LargestOddsEmpty(ms: multiset<char>)
        requires largestOdd(ms) == multiset{}
        ensures allEven(ms)
    {
        var candidates: set<char> := set x | charCountOdd(x,ms) && (forall y :: charCountOdd(y,ms) ==> ms[x] >= ms[y]);
        assert |candidates| == 0;
        var odds := set x | charCountOdd(x, ms);
        assert odds == {} by {
            if odds != {} {
                var zs := set z | z in odds :: ms[z];
                var z :| charCountOdd(z, ms);
                assert z in odds;
                assert ms[z] in zs;
                ThereIsAMaximum(zs);
                var max :| max in zs && forall y :: y in zs ==> max >= y;
                var q :| q in odds && ms[q] == max;
                assert charCountOdd(q, ms);
                forall y | charCountOdd(y, ms)
                    ensures max >= ms[y]
                {
                    assert y in odds;
                    assert ms[y] in zs;
                }
                assert q in candidates;
            }
        }
        if !(forall x :: ms[x] % 2 == 0) {
            var x :| ms[x]%2 ==1;
            assert x in odds;
        }
    }

    ghost function largestOdd(ms: multiset<char>) : multiset<char> 
        ensures largestOdd(ms) != multiset{} ==> forall x :: x in largestOdd(ms) ==> ms[x] % 2 == 1
        // ensures largestOdd(ms) == multiset{} ==> forall x :: ms[x] % 2 == 0
    {
        var candidates: set<char> := set x | charCountOdd(x,ms) && (forall y :: charCountOdd(y,ms) ==> ms[x] >= ms[y]);
        var stub: multiset<char> := multiset{};
        if |candidates| == 0 then 
            multiset{}
        else var x :| x in candidates; stub[x := ms[x]]
    }

    lemma noLargestNoOdds(ms: multiset<char>)
        requires (set x | charCountOdd(x, ms) && (forall y :: charCountOdd(y, ms) ==> ms[x] >= ms[y])) == {}
        ensures allEven(ms)
    {
        var largest := (set x | charCountOdd(x, ms) && (forall y :: charCountOdd(y, ms) ==> ms[x] >= ms[y]));
        assert largest == {};
        if !(forall x :: x in ms ==> ms[x] % 2 == 0) {
            var y :| y in ms && ms[y] % 2 == 1;
            var  odds := set x | charCountOdd(x, ms);
            assert y in odds;
            var sizes := set x | charCountOdd(x, ms) :: ms[x];
            assert ms[y] in sizes;
            ThereIsAMaximum(sizes);
            var max :| max in sizes && forall z :: z in sizes ==> max >= z;
            var q :| q in odds && ms[q] == max;
            assert charCountOdd(q, ms);
            forall x | charCountOdd(x, ms)
                ensures ms[q] >= ms[x]
            {
                assert x in odds;
                assert ms[x] in sizes;
            }
            assert q in largest;
        }
    }

    lemma largestExistsRev(ms: multiset<char>)
        requires exists y :: charCountOdd(y, ms) && forall x :: charCountOdd(x, ms) && ms[y] >= ms[x]
        ensures (set x | charCountOdd(x, ms)) != {}
    {
        var res := (set x | charCountOdd(x, ms));
        var y :| exists y :: y in ms && ms[y] % 2 == 1 && forall x :: x in ms && ms[x] % 2 == 1 && ms[y] >= ms[x];
        assert y in res;
    }

    lemma ThereIsAMaximum(s: set<int>)
        requires s != {}
        ensures exists x :: x in s && forall y :: y in s ==> x >= y
    {
        assert s != {};
        var x :| x in s;
        if s == {x} {
        } else {
            var s' := s - {x};
            assert s == s' + {x};
            ThereIsAMaximum(s');
        }
    }

    predicate charCountOdd(x: char, ms: multiset<char>) {
        x in ms && ms[x] % 2 == 1
    }

    predicate charCountEven(x: char, ms: multiset<char>) {
        x in ms && ms[x] % 2 == 0
    }

    lemma LargestExists(ms: multiset<char>) returns (x: char)
        requires (set x | charCountOdd(x, ms)) != {}
        ensures charCountOdd(x, ms) && (forall y :: charCountOdd(y, ms) ==> ms[x] >= ms[y])
    {
        var odds := set x| charCountOdd(x, ms);
        assert odds != {};
        var counts := set x | charCountOdd(x, ms) :: ms[x];
        x :| x in odds;
        assert ms[x] in counts;
        assert counts != {};
        ThereIsAMaximum(counts);
        var max :| max in counts && forall y :: y in counts ==> max >= y;
        var q :| q in odds && ms[q] == max;
        assert charCountOdd(q, ms);
        forall y | charCountOdd(y, ms)
            ensures ms[q] >= ms[y]
        {
            assert y in odds;
            assert ms[y] in counts;
        }
        assert charCountOdd(q, ms) && (forall y :: charCountOdd(y, ms) ==> ms[q] >= ms[y]);
        return q;
    }

    predicate allEven(ms: multiset<char>) {
        forall x :: x in ms ==> ms[x] % 2 ==0
    }

    ghost function evenPlusRectEvens(ms: multiset<char>): multiset<char> 
        // ensures forall x :: x in evenPlusRectEvens(ms) ==> evenPlusRectEvens(ms)[x] % 2 ==0
        ensures allEven(evenPlusRectEvens(ms))
        ensures evenPlusRectEvens(ms) <= ms
        ensures forall k :: k in ms && ms[k] % 2 == 0 ==> evenPlusRectEvens(ms)[k] == ms[k]
        ensures forall k :: k in ms && ms[k] % 2 == 1 ==> evenPlusRectEvens(ms)[k] == ms[k] - 1
    {
        if |ms| == 0 then multiset{} else
        var x :| x in ms;
        var stub: multiset<char> := multiset{};
        if ms[x] % 2 == 0 then
            stub[x := ms[x]]+evenPlusRectEvens(ms[x := 0])
        else
            stub[x := ms[x]-1]+evenPlusRectEvens(ms[x :=0])
    }

    ghost function largePalindromeMultiset(str: string): multiset<char>
        ensures largestOdd(multiset(str)) == multiset{} ==> allEven(largePalindromeMultiset(str))
        // ensures largestOdd(multiset(str)) != multiset{} ==> exists k :: k in largePalindromeMultiset(str) && largePalindromeMultiset(str)[k] % 2 ==1 && 
        ensures largestOdd(multiset(str)) != multiset{} ==> exists k :: charCountOdd(k,largePalindromeMultiset(str)) && 
            (forall y :: charCountOdd(y, multiset(str)) ==> largePalindromeMultiset(str)[k] >= multiset(str)[y] )
            && forall kk :: kk != k && kk in largePalindromeMultiset(str) ==> charCountEven(kk, largePalindromeMultiset(str))
        ensures largePalindromeMultiset(str) <= multiset(str)
        ensures forall zz :: zz in largePalindromeMultiset(str) && largePalindromeMultiset(str)[zz] % 2 == 0 ==> largePalindromeMultiset(str)[zz] <= multiset(str)[zz]
        ensures forall zz :: zz in largePalindromeMultiset(str) && largePalindromeMultiset(str)[zz] % 2 == 0 ==> largePalindromeMultiset(str)[zz] == multiset(str)[zz]||largePalindromeMultiset(str)[zz] == multiset(str)[zz]-1
        ensures forall zz :: zz in largePalindromeMultiset(str) && multiset(str)[zz] % 2 == 0 ==> largePalindromeMultiset(str)[zz] == multiset(str)[zz]
        // ensures forall zz :: zz in largePalindromeMultiset(str) && multiset(str)[zz] % 2 == 1 ==> largePalindromeMultiset(str)[zz] == multiset(str)[zz] -1
    {
        var ms := multiset(str);
        var largestOdds := largestOdd(ms);
        if largestOdds != multiset{} then 
            var x :| x in largestOdds;
            assert x !in ms-largestOdds;
            assert x !in evenPlusRectEvens(ms-largestOdds);
            assert ms[x] % 2 == 1;
            assert forall y :: y in ms && ms[y] % 2 == 1 ==> ms[x] >= ms[y];
            assert x in largestOdds+evenPlusRectEvens(ms-largestOdds);
            largestOdds+evenPlusRectEvens(ms-largestOdds)
        else evenPlusRectEvens(ms) 
    }

    lemma AllEvenOrOneOdd(s: string) 
        requires IsPalindrome(s)
        ensures allEven(multiset(s)) || exists k :: charCountOdd(k, multiset(s)) && forall y :: y != k && y in multiset(s) ==>charCountEven(y,multiset(s))
        ensures |s|%2==0 ==> allEven(multiset(s))
        ensures |s|%2==1 ==> charCountOdd(s[|s|/2],multiset(s))
    {
        ip2(s);
        if |s| % 2 == 0 {
            assert s == s[..|s|/2]+s[(|s|/2)..];
            assert multiset(s[..|s|/2]) == multiset(s[(|s|/2)..]);
        }else{
            assert s == s[..|s|/2]+[s[|s|/2]]+s[(|s|/2+1)..];
            assert multiset(s[..|s|/2]) == multiset(s[(|s|/2+1)..]);
            assert charCountOdd(s[|s|/2], multiset(s));
        }
    }


    lemma twoInMultisetGreaterThan1(s: string, i: int, j: int, c: char)
        requires i != j
        requires 0 <= i < |s|
        requires 0 <= j < |s|
        requires s[i] == c
        requires s[j] == c
        ensures multiset(s)[c] > 1
    {
        if i < j {
            assert s==s[..i]+[c]+s[(i+1)..j]+[c]+s[(j+1)..];
        }else{
            assert s==s[..j]+[c]+s[(j+1)..i]+[c]+s[(i+1)..];

        }
    }

    lemma {:vcs_split_on_every_assert} PalindromeStringExists(ms: multiset<char>) returns (s: string)
        requires allEven(ms) || exists k :: charCountOdd(k, ms) && forall y :: y != k && y in ms ==>charCountEven(y, ms)
        ensures multiset(s) == ms
        ensures IsPalindrome(s)
        ensures allEven(ms) ==> |s| % 2 == 0
        ensures !allEven(ms) ==> |s| % 2 == 1
    {
        if ms != multiset{} {
            var x :|  x in ms;
            if charCountEven(x, ms) {
                if allEven(ms) {
                    var s' := PalindromeStringExists(ms[x := 0]);
                    PalindromePlusRep(s', x, ms[x]/2);
                    s := rep(x, ms[x]/2)+s'+rep(x, ms[x]/2);
                    assert ms == multiset(s);
                    assert |s'| % 2 == 0;
                    calc {
                        |s|;
                        |rep(x, ms[x]/2)|+|s'|+|rep(x, ms[x]/2)|;
                        |rep(x, ms[x]/2)|+|rep(x, ms[x]/2)|+|s'|;
                        ms[x]+|s'|;
                    }
                    assert |s| % 2 == 0;
                }else{
                    assert exists k :: charCountOdd(k, ms) && forall y :: y != k && y in ms ==> charCountEven(y, ms);
                    var k :| charCountOdd(k, ms);
                    assert charCountOdd(k, ms[x:=0]) && forall y :: y != k && y in ms[x := 0] ==> charCountEven(y, ms[x := 0]);
                    var s' := PalindromeStringExists(ms[x := 0]);
                    PalindromePlusRep(s', x, ms[x]/2);
                    s := rep(x, ms[x]/2)+s'+rep(x, ms[x]/2);
                    assert ms == multiset(s);
                    assert |s'| % 2 == 1;
                    calc {
                        |s|;
                        |rep(x, ms[x]/2)|+|s'|+|rep(x, ms[x]/2)|;
                        |rep(x, ms[x]/2)|+|rep(x, ms[x]/2)|+|s'|;
                        ms[x]+|s'|;
                    }
                    assert |s| % 2 == 1;
                }

            }else{
                var s' := PalindromeStringExists(ms[x := 0]);
                assert s' == s'[0..|s'|/2]+s'[|s'|/2..];
                PalindromePlusRepOdd(s', x, ms[x]);
                s := s'[0..|s'|/2]+rep(x, ms[x])+s'[|s'|/2..];
                assert ms == multiset(s);
                assert |s'| % 2 == 0;
                calc {
                    |s|;
                    |s'[0..|s'|/2]|+|rep(x, ms[x])|+|s'[|s'|/2..]|;
                    |s'[0..|s'|/2]|+|s'[|s'|/2..]|+|rep(x, ms[x])|;
                    |s'|+|rep(x, ms[x])|;
                }
                assert |s| % 2 == 1;
            }
        }else{
            s := "";
            assert ms == multiset(s);
            assert allEven(multiset(s));
            assert IsPalindrome(s);
            assert |s| % 2 == 0;
        }
    }


    lemma PalindromeNotPalindrome(s: string, c: char)
        requires IsPalindrome(s)
        requires c in s && multiset(s)[c] == 1
        requires |s| % 2 == 0 || s[|s|/2] != c
        ensures !IsPalindrome(s)
    {
        PalindromeLeft(s);
        assert |s| > 0;
        if |s| % 2 == 0 {
            var i :| 0 <= i < |s| && s[i] == c;
            var j := |s|-i-1;
            assert j != i;
            if s[j] == c {
                twoInMultisetGreaterThan1(s,i,j,c);
                assert false;
            }
            assert s[|s|-i-1] != c;

        }else if s[|s|/2] != c {
            var i :| 0 <= i < |s| && s[i] == c;
            var j := |s|-i-1;
            assert j != i;
            if s[j] == c {
                twoInMultisetGreaterThan1(s,i,j,c);
                assert false;
            }
            assert s[|s|-i-1] != c;

        }
    }

    lemma {:verify } PalindromeNotPalindromeAgain(s: string, c: char, n: nat)
        requires IsPalindrome(s)
        requires n %2 == 1
        requires c in s && multiset(s)[c] == n
        requires |s| % 2 == 0 || s[|s|/2] != c
        ensures !IsPalindrome(s)
    {
        PalindromeLeft(s);
        AllEvenOrOneOdd(s);
        if |s| % 2 == 0 {
            // assert !allEven(multiset(s));
            assert false;
        }else{
            assert |s| % 2 == 1;
        }
    }

    lemma multisetPlusX<T>(ms: multiset<T>, x: T, count: nat)
    requires x !in ms
    ensures |ms[x := count]| == |ms|+count
    {}

    lemma multisetMinusX<T>(ms: multiset<T>, x: T, count: nat)
    requires x in ms
    requires ms[x] == count
    ensures |ms[x := 0]| == |ms|-count
    {}

    lemma charCountOddStillLess(ss: string, str: string, keychar: char)
        requires ss in allPalindromSubStrings(str)
        requires !allEven(multiset(ss))
        requires charCountOdd(keychar, multiset(str))
        requires |ss| % 2 == 1
        requires keychar == ss[|ss|/2]
        requires charCountOdd(keychar, multiset(ss)) && forall k :: k in multiset(ss) && k != keychar ==> multiset(ss)[k] % 2 == 0
        ensures |ss| <= |largePalindromeMultiset(str)|
    {

        var lpm := largePalindromeMultiset(str);
        var odds := (set x | charCountOdd(x, multiset(str)));
        assert keychar in odds;
        assert odds != {};
        var largestOdds := largestOdd(multiset(str));
        var x := LargestExists(multiset(str));

        var candidates: set<char> := set x | charCountOdd(x,multiset(str)) && (forall y :: charCountOdd(y,multiset(str)) ==> multiset(str)[x] >= multiset(str)[y]);
        assert x in candidates;
        // assert |candidates| > 0;
        // assert largestOdds != multiset{};
        var lo :| lo in largestOdds && lo in lpm;
        // assert multiset(ss)[keychar] <= lpm[lo] == multiset(str)[lo];
        // assert multiset(ss)[keychar := 0][lo := 0] < lpm;
        multisetSubsetSmaller(lpm, multiset(ss)[keychar := 0][lo := 0]);
        // assert |multiset(ss)[keychar := 0][lo := 0]| < |lpm|;
        if lo != keychar {
            if lo in multiset(ss) {
                calc {
                    |multiset(ss)[keychar := 0][lo := 0]|;
                    {multisetMinusX(multiset(ss), lo, multiset(ss)[lo]);}
                    |multiset(ss)[keychar := 0]|-multiset(ss)[lo];
                    {multisetMinusX(multiset(ss), keychar, multiset(ss)[keychar]);}
                    |multiset(ss)|-multiset(ss)[keychar]-multiset(ss)[lo];
                }
                if keychar in lpm {
                    // assert multiset(ss)[keychar := 0] <= lpm;
                // assert multiset(ss)[keychar := 0][lo := 0] < lpm[lo:=0];
                // assert multiset(ss)[keychar := 0][lo := 0] <= lpm[keychar:=0][lo:=0];
                // multisetSubsetSmaller(lpm[lo := 0], multiset(ss)[keychar := 0][lo := 0]);
                multisetSubsetSmallerEqual(lpm[keychar:=0][lo := 0], multiset(ss)[keychar := 0][lo := 0]);
                multisetPlusX(lpm[lo := 0], lo, lpm[lo]);
                multisetPlusX(lpm[keychar:=0][lo := 0], keychar, lpm[keychar]);
                assert |lpm| == |lpm[keychar:=0][lo := 0]|+lpm[keychar]+lpm[lo];
                // assert |multiset(ss)[keychar := 0][lo := 0]| < |lpm[lo := 0]|;
                assert |multiset(ss)[keychar := 0][lo := 0]| + multiset(ss)[keychar]+multiset(ss)[lo] == |multiset(ss)|;
                // assert multiset(ss)[lo]+1 <= lpm[lo];
                // assert multiset(ss)[keychar]-1 <= lpm[keychar];
                // assert |multiset(ss)[keychar := 0][lo := 0]| + multiset(ss)[keychar]-1+multiset(ss)[lo]+1 <= |lpm[keychar:=0][lo := 0]|+lpm[keychar]+lpm[lo];
                    assert |multiset(ss)| <= |lpm|;
                }else{
                    assert multiset(ss)[lo]+1 <= lpm[lo];
                    assert multiset(ss)[keychar] == 1;
                    assert multiset(ss)[keychar := 0][lo := 0] <= lpm[keychar:=0][lo:=0];
                    multisetSubsetSmallerEqual(lpm[keychar:=0][lo := 0], multiset(ss)[keychar := 0][lo := 0]);

                    assert |multiset(ss)| <= |lpm|;
                }
            }else{
                // calc {
                //     |multiset(ss)[keychar := 0]|;
                //     {multisetMinusX(multiset(ss), keychar, multiset(ss)[keychar]);}
                //     |multiset(ss)|-multiset(ss)[keychar];
                // }
                if keychar in lpm {

                    // assert multiset(ss)[keychar := 0] < lpm[lo:=0];
                    multisetSubsetSmaller(lpm[lo:=0], multiset(ss)[keychar := 0]);
                    // assert |multiset(ss)| == |multiset(ss)[keychar := 0]| + multiset(ss)[keychar];
                    multisetPlusX(lpm[lo := 0], lo, lpm[lo]);
                    // assert |lpm| == |lpm[lo := 0]| + lpm[lo];
                    // assert |multiset(ss)[keychar := 0]| + multiset(ss)[keychar] <= |lpm[lo:=0]|+lpm[lo];
                    assert |multiset(ss)| <= |lpm|;
                    // assert |multiset(ss)[keychar := 0]| < |lpm[lo:=0]|;
                }else{

                    assert |multiset(ss)| <= |lpm|;
                }
            }
        }else{
            assert multiset(ss) <= lpm;
            multisetSubsetSmallerEqual(lpm, multiset(ss));
        }
    }


    lemma lpmGreaterAllPalindromes(str: string)
        ensures forall ss :: ss in allPalindromSubStrings(str) ==> |ss| <= |largePalindromeMultiset(str)|
    {
        var lpm := largePalindromeMultiset(str);
        assert lpm <= multiset(str);
        forall ss | ss in allPalindromSubStrings(str) 
            ensures |ss| <= |lpm|
        {
            assert |ss| == |multiset(ss)|;
            AllEvenOrOneOdd(ss);
            if allEven(multiset(ss)) {
                assert multiset(ss) <= multiset(str);
                assert multiset(ss) <= lpm;
                multisetSubsetSmallerEqual(lpm, multiset(ss));
                assert |multiset(ss)| <= |lpm|;
            }else{
                assert |ss| % 2 == 1;
                assert !allEven(multiset(ss));
                assert multiset(ss) <= multiset(str);
                var keychar := ss[|ss|/2];
                assert charCountOdd(keychar, multiset(ss)) && forall k :: k in multiset(ss) && k != keychar ==> multiset(ss)[k] % 2 == 0;
                assert keychar in str;

                if charCountOdd(keychar, multiset(str)) {
                    var odds := (set x | charCountOdd(x, multiset(str)));
                    assert keychar in odds;
                    charCountOddStillLess(ss, str, keychar);
                } else if charCountEven(keychar, multiset(str)) {
                    assert keychar in lpm;
                    assert multiset(ss) <= lpm;
                    multisetSubsetSmallerEqual(lpm, multiset(ss));
                    assert |ss| <= |lpm|;
                }
                assert |ss| <= |lpm|;

            }

            assert |ss| <= |lpm|;
        }
        

    }

    lemma LongestPalindromeFromString(s: string)
        ensures exists s' :: IsPalindrome(s') && forall ss :: ss in allPalindromSubStrings(s) ==> |ss| <= |s'|
    {
        var lpm := largePalindromeMultiset(s);
        lpmGreaterAllPalindromes(s);
        var s' := PalindromeStringExists(lpm);
    }
                // if keychar !in lpm {
                //     assert multiset(str)[keychar] == 1;
                //     var largestOdds := largestOdd(multiset(str));
                //     var lo :|  assume true && lo in largestOdds && lo in lpm;
                //     assert multiset(ss)[keychar] <= lpm[lo] <= multiset(str)[lo];
                //     assert |multiset(ss)[keychar := 0]| == |multiset(ss)|-1;

                //     assert charCountOdd(keychar, multiset(ss));
                //     assert allEven(multiset(ss)[keychar := 0]);
                //     assert multiset(ss)[keychar := 0] <= lpm;
                // }else{
                //     assert keychar in lpm;

                // }
                // assert multiset(ss) <= lpm;
                // assert |multiset(ss)| <= |lpm|;
                // var largestOdds := largestOdd(multiset(str));
                // if largestOdds == multiset{} {
                //     LargestOddsEmpty(largestOdds);
                //     /*
                //     I assumed that if largestOdds was empty then the substring odds would be empty
                //     but it could be the substring odd char was an even char in the original string
                //     */
                //     // assert false;
                // }else{
                // var lo :| lo in largestOdds && lo in lpm;
                // var k :| charCountOdd(k, multiset(ss)) && forall y :: y != k && y in multiset(ss) ==> charCountEven(y, multiset(ss));
                // var j :| charCountOdd(j, lpm) && (forall y :: charCountOdd(y, multiset(str)) ==> lpm[j] >= multiset(str)[y] ) && forall kk :: kk != j && kk in lpm ==> charCountEven(kk, lpm);
                // assert lo == j;
                // // assert charCountOdd(k ,multiset(str));
                // // if k in LargestExists
                // // assert multiset(ss)[k] <= lpm[j];

                // var stub: multiset<char> := multiset{};
                // var ssm := multiset(ss)-stub[k := multiset(ss)[k]];
                // assert allEven(ssm);
                // assert ssm <= lpm;
                // if charCountEven(k, multiset(str)) {
                //     assert multiset(ss)[k] < lpm[k];
                //     assert multiset(ss) <= lpm;
                //     multisetSubsetSmallerEqual(lpm, multiset(ss));
                //     assert |multiset(ss)| <= |lpm|;
                // }else {
                //     /**
                //         "aaabbbxxzzqp"
                //         lpm == "aaabbxxzz"
                //         j=="a"
                //         k=="b"
                //         ss == "bbbaaxxzz"
                //         ss == "azbxqxbza"
                //     */
                //     assert charCountOdd(k, multiset(str));
                //     assert multiset(ss)[k] <= lpm[j];
                //     if k in lpm {

                //     }else{

                //     }
                //     // assert multiset(ss) <= lpm;
                //     // multisetSubsetSmallerEqual(lpm, multiset(ss));
                // }
                // }
    // lemma largestAllEven(s: string)
    //     ensures forall ss :: ss in allStrings(multiset(s)) && allEven(multiset(ss)) ==> |ss| <= |evenPlusRectEvens(multiset(s))|
    // {

    // }
}