include "../lib/seq.dfy"
include "../lib/sets.dfy"
include "../lib/Trie.dfy"

module LongestCommonPrefix {
    import opened Tries
    import opened SeqCustom
    import opened SetCustom

    predicate IsCommonPrefix(prefix: string, strs: set<string>)
    {
        forall words :: words in strs ==> IsPrefix(prefix, words)
    }

    ghost function AllPrefixes(strs: set<string>): iset<string>
    {
        if strs == {} then
            iset{}
        else
            var x :| x in strs;
            // (set w | IsPrefix(w, x)) + AllPrefixes(strs - {x})
            (iset w | IsPrefix(w, x)) + AllPrefixes(strs - {x})
    }

    function ToSet(strs: seq<string>): set<string>
    {
        if strs == [] then
            {}
        else
            {strs[0]} + ToSet(strs[1..])
    }

    lemma ToSetConcat(s1: seq<string>, s2: seq<string>)
        ensures ToSet(s1 + s2) == ToSet(s1) + ToSet(s2)
    {
        if s1 == [] {
            assert s1 + s2 == s2;
        } else {
            assert s1 == [s1[0]] + s1[1..];
            ToSetConcat(s1[1..], s2);
            assert [s1[0]]+(s1[1..] + s2) == s1 + s2;
        }
    }

    lemma ToSetHasAll(strs: seq<string>)
        ensures forall x :: x in strs ==> x in ToSet(strs)
    {}

    twostate lemma AllFreshUnionFresh(ss: set<set<Trie>>)
        requires forall s :: s in ss ==> forall t :: t in s ==> t.Valid()
        requires forall s :: s in ss ==> fresh(s)
        ensures fresh(Union(ss))
    {

    }



    // twostate predicate UnionFresh(t: Trie)
    //     requires t.Valid()
    //     requires forall k :: k in t.children.Keys ==> fresh(t.children[k].repr)
    // {
    //    fresh(Union(set k | k in t.children.Keys :: t.children[k].repr)) 
    // }

    method {:vcs_split_on_every_assert} longestCommonPrefix(strs: seq<string>) returns (prefix: string)
        requires strs != []
        requires forall i :: 0 <= i < |strs| ==> strs[i] != ""
        ensures IsCommonPrefix(prefix, ToSet(strs))
        ensures forall prefixes :: prefixes in AllPrefixes(ToSet(strs)) ==> |prefixes| <= |prefix|
    {
        var trie := new Trie();
        assert fresh(trie.repr);
        assert trie.Valid();
        assert fresh(trie);
        label Begin:
        for i := 0 to |strs| 
            invariant allocated(trie)
            invariant "" !in strs[0..i]
            // invariant trie.words != {} ==> trie.children.Keys != {}
            invariant fresh(trie)
            invariant fresh(trie.repr)
            invariant forall k :: k in trie.children.Keys ==> fresh(trie.children[k]) && fresh(trie.children[k].repr)
            invariant trie.children.Keys == {} ==> fresh(trie.repr)
            invariant trie.children.Keys != {} ==> fresh(trie.repr)
            // invariant fresh(Union(set k | k in trie.children.Keys :: trie.children[k].repr)) /// <<EXPLODES!
            invariant fresh(Union(trie.ReprSet()))
            // invariant fresh(trie.repr-old@Begin(trie.repr))
            invariant 0 <= i <= |strs|
            invariant trie.Valid()
            invariant trie.words == ToSet(strs[0..i])
            modifies  trie, trie.repr
        {
            assert strs == strs[0..i] + strs[i..];
            // label PreInsert:
            if trie.children.Keys == {} {
                // assert "" !in trie.words;
                // assert trie.words == {};
            } else {
                UnionHasAll(set k | k in trie.children.Keys :: trie.children[k].repr);
                NotInAllNotInUnion(set k | k in trie.children.Keys :: trie.children[k].repr, trie);
                assert trie !in Union(set k | k in trie.children.Keys :: trie.children[k].repr);
                assert trie.repr == {trie} + Union(set k | k in trie.children.Keys :: trie.children[k].repr);
                assert Union(set k | k in trie.children.Keys :: trie.children[k].repr) < trie.repr;
                ghost var foo := set key | key in trie.children.Keys :: trie.children[key].repr;
                // assert foo == ReprSet(trie);

                // AllFreshUnionFresh(trie.ReprSet());
                // assert fresh(Union(set k | k in trie.children.Keys :: trie.children[k].repr));
                // assert trie.words == Union(set k | k in trie.children.Keys :: trie.children[k].repr);
            }
            trie.insertRecursive(strs[i]);
            assert strs[0..i+1] == strs[0..i] + [strs[i]];
            ToSetConcat(strs[0..i], [strs[i]]);
            ToSetHasAll(strs[0..i+1]);
            // assert trie.words == old@PreInsert(trie.words) + {strs[i]};
        }
        assert strs == strs[0..|strs|];
        assert ToSet(strs) == ToSet(strs[0..|strs|]);
        assert ToSet(strs) == trie.words;
        prefix := longestCommonPrefixRec(trie, "");
    }

    method {:verify false} longestCommonPrefixRec(t: Trie, prefix: string) returns (prefix': string)
        requires t.Valid()
        requires IsCommonPrefix(prefix, t.words)
        ensures IsCommonPrefix(prefix', t.words)
        ensures forall prefixes :: prefixes in AllPrefixes(t.words) ==> |prefixes| <= |prefix|
    {
        if |t.children.Keys| == 1 {
            if t.isWord {
                return prefix;
            }else{
                var key :| key in t.children.Keys;
                prefix' := longestCommonPrefixRec(t.children[key], prefix + [key]);
                return prefix';
            }
        }
        return prefix;
    }

}