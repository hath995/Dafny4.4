include "../lib/seq.dfy"
include "../lib/Trie.dfy"

module LongestCommonPrefix {
    import opened Tries
    import opened SeqCustom

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

    method longestCommonPrefix(strs: seq<string>) returns (prefix: string)
        requires strs != []
        ensures IsCommonPrefix(prefix, ToSet(strs))
        ensures forall prefixes :: prefixes in AllPrefixes(ToSet(strs)) ==> |prefixes| <= |prefix|
    {
        var trie := new Trie();
        label Begin:
        for i := 0 to |strs| 
            invariant allocated(trie)
            invariant fresh(trie.repr-old@Begin(trie.repr))
            invariant 0 <= i <= |strs|
            invariant trie.Valid()
            invariant trie.words == ToSet(strs[0..i])
            modifies trie.repr
        {
            assert strs == strs[0..i] + strs[i..];
            label PreInsert:
            trie.insertRecursive(strs[i]);
            assert strs[0..i+1] == strs[0..i] + [strs[i]];
            ToSetConcat(strs[0..i], [strs[i]]);
            ToSetHasAll(strs[0..i+1]);
            assert trie.words == old@PreInsert(trie.words) + {strs[i]};
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
        return "";
    }

}