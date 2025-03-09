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
            assert [s1[0]]+(s1[1..] + s2) == s1 + s2;
            ToSetConcat(s1[1..], s2);
        }
    }


    lemma ToSetHasAll(strs: seq<string>)
        ensures forall x :: x in strs ==> x in ToSet(strs)
    {}

    lemma prefixInAllPrefixes(prefix: string, strs: set<string>)
        requires strs != {}
        requires IsCommonPrefix(prefix, strs)
        ensures prefix in AllPrefixes(strs)
    {

    }

    ghost function WordsSlice(strs: set<string>): set<string>
        requires forall s :: s in strs ==> s != ""
    {
        if strs == {} then
            {}
        else
            var x :| x in strs;
            {x[1..]} + WordsSlice(strs - {x})
    }

    function WordRest(prefix: string, words: set<string>): set<string>
    {
        set w | w in words :: prefix + w
    }

    lemma InWordRest(s: string, prefix: string, suffix: string, words: set<string>)
        requires s == prefix + suffix
        requires suffix in words
        ensures s in WordRest(prefix, words)
    {
    }

    lemma WordRestSize(prefix: string, words: set<string>)
       ensures |WordRest(prefix, words)| == |words|
    {
        if words == {} {
            assert WordRest(prefix, words) == {};
            assert |WordRest(prefix, words)| == |words|;
        } else {
            var x :| x in words;
            WordRestSize(prefix, words - {x});
            assert |words| == |words - {x}| + 1;
            assert |words - {x}| == |WordRest(prefix, words - {x})|;
            assert WordRest(prefix, words) == WordRest(prefix, words - {x}) + {prefix + x};
            assert prefix + x !in WordRest(prefix, words - {x}) by {
                if prefix + x in WordRest(prefix, words - {x}) {
                    if words - {x} == {} {
                        assert false;
                    }
                    var y :| y in words - {x} && prefix + y == prefix + x;
                    assert y == (prefix+x)[|prefix|..];
                    assert y == x;
                    // assert x in words - {x};
                    assert false;
                }
            }
            assert prefix + x in WordRest(prefix, words);
            assert |WordRest(prefix, words)| == |WordRest(prefix, words - {x})| + 1;
            assert |WordRest(prefix, words)| == |words|;
        }
    }

    ghost predicate LongestPrefix(prefix: string, strs: set<string>)
    {
        IsCommonPrefix(prefix, strs) && forall prefixes :: prefixes in AllPrefixes(strs) && IsCommonPrefix(prefixes, strs) ==> |prefixes| <= |prefix|
    }

    lemma LongestPredicateUnique(prefixA: string, prefixB: string, strs: set<string>)
        requires strs != {}
        requires LongestPrefix(prefixA, strs)
        requires LongestPrefix(prefixB, strs)
        ensures prefixA == prefixB
    {}




    lemma shortestWordsIsLongestedPrefix(strs: set<string>, short: string, long: string)
        requires short in strs
        requires long in strs
        requires |long| > |short|
        requires IsCommonPrefix(short, strs)
        ensures !IsCommonPrefix(long, strs)
    {}

    lemma longestPrefixIsShortestWord(strs: set<string>, short: string)
        requires short in strs
        requires IsCommonPrefix(short, strs)
        ensures LongestPrefix(short, strs)
    {}

    lemma WordRestChild(t: Trie, key: char)
        requires t.Valid()
        requires key in t.children.Keys
        ensures WordRest([key], t.children[key].words) == set w | w in t.words && |w| > 0 && w[0] == key
    {
        var keyWords := set w | w in t.words && |w| > 0 && w[0] == key;
        WordRestSize([key], t.children[key].words);
        if t.children[key].words == {} {
            assert key in t.firstChars;
            var w :| w in t.words && |w| > 0 && w[0] == key;
            assert w in t.words;
            assert w in keyWords;
            assert w[1..] in t.children[key].words;
            assert false;
        } else {
            forall kw | kw in keyWords
                ensures kw in WordRest([key], t.children[key].words)
            {
                assert kw in t.words;
                assert kw[0] == key;
                assert kw[1..] in t.children[key].words;
                assert kw == [key] + kw[1..];
                assert kw in WordRest([key], t.children[key].words);
            }

            forall w | w in WordRest([key], t.children[key].words)
                ensures w in keyWords
            {
                var tw :| tw in t.children[key].words && [key] + tw == w;
                assert tw in t.children[key].words;
                assert |w| > 0;
                assert w[0] == key;
                forall kw | kw in t.words && |kw| > 0 && kw[0] == key && kw != w
                    ensures kw[1..] != tw
                {
                }
                assert w in t.words by {
                    if w !in t.words {
                        assert tw == w[1..];
                        assert tw !in t.children[key].words;
                        assert false;
                    }
                }
            }
        }
    }

            // invariant trie.words != {} ==> trie.children.Keys != {}
            // invariant fresh(trie)
            // invariant fresh(trie.repr)
            // invariant forall k :: k in trie.children.Keys ==> fresh(trie.children[k]) && fresh(trie.children[k].repr)
            // invariant trie.children.Keys == {} ==> fresh(trie.repr)
            // invariant trie.children.Keys != {} ==> fresh(trie.repr)
            // invariant fresh(Union(set k | k in trie.children.Keys :: trie.children[k].repr)) /// <<EXPLODES!
            // invariant fresh(Union(trie.ReprSet()))
            // invariant fresh(trie.repr-old@Begin(trie.repr))
    lemma  {:vcs_split_on_every_assert} longestPrefixOfTrieWithMultipleKeys(t: Trie, prefix: string, words: set<string>)
        requires t.children.Keys != {}
        requires |t.children.Keys| > 1
        requires "" !in t.words
        requires t.Valid()
        requires words == WordRest(prefix, t.words)
        requires IsCommonPrefix(prefix, words)
        ensures LongestPrefix(prefix, words)
    {

        if longerPrefix :| longerPrefix in AllPrefixes(words) && IsCommonPrefix(longerPrefix, words) && |longerPrefix| > |prefix| {
            var c := longerPrefix[|prefix|];
            // assert c in t.children.Keys;
            assert t.children.Keys-{c} != {} by {
                if (t.children.Keys-{c}) == {} {
                    assert (t.children.Keys-{c})+{c} == {} + {c};
                    assert t.children.Keys == {c};
                    assert |t.children.Keys| == 1;
                    assert false;
                }
            }
            var b :| b in t.children.Keys && b != c;
            var bword :| bword in t.words && bword[0] == b && |bword| > 0;
            assert bword == [b] + bword[1..];
            var bwords := WordRest(prefix+[b], t.children[b].words);
            assert t.children[b].words == set w | w in t.words && w[0]==b :: w[1..];
            InWordRest(prefix + bword, prefix+[b], bword[1..], t.children[b].words);
            
            // assert  bwords != {};
            assert bwords < words by {
                forall w | w in bwords
                    ensures w in words
                {
                    var tw :| tw in t.children[b].words && prefix+[b] + tw == w;
                    var bw := [b] + tw;
                    var bs := set bw | bw in t.words && |bw| > 0 && bw[0] == b;
                    WordRestChild(t, b);
                    assert bs == WordRest([b], t.children[b].words);
                    assert bw in bs by {
                        if bw !in bs {
                            assert bw[0] == b;
                            assert bw[1..] !in t.children[b].words;
                            assert false;
                        }
                    }
                    assert prefix + bw == w;
                }
            }
            assert false;
        }
    }

    method longestCommonPrefix(strs: seq<string>) returns (prefix: string)
        requires strs != []
        ensures LongestPrefix(prefix, ToSet(strs))
    {
        var trie := new Trie();
        label Begin:
        for i := 0 to |strs| 
            invariant allocated(trie)
            invariant fresh(trie.repr - old@Begin(trie.repr))
            invariant 0 <= i <= |strs|
            invariant trie.Valid()
            invariant trie.words == ToSet(strs[0..i])
        {
            trie.insertRecursive(strs[i]);
            assert strs[0..i+1] == strs[0..i] + [strs[i]];
            ToSetConcat(strs[0..i], [strs[i]]);
        }
        assert strs == strs[0..|strs|];
        assert ToSet(strs) == ToSet(strs[0..|strs|]);
        assert ToSet(strs) == trie.words;
        assert WordRest("", ToSet(strs)) == ToSet(strs) by {
            forall w | w in ToSet(strs)
                ensures "" + w in ToSet(strs)
            {
                assert "" + w == w;
            }

            forall w | w in ToSet(strs)
                ensures w in WordRest("", ToSet(strs))
            {
                assert "" + w == w;
                assert w in WordRest("", ToSet(strs));
            }
        }
        prefix := longestCommonPrefixRec(trie, "", trie.words);
    }

    method longestCommonPrefixRec(t: Trie, prefix: string, ghost words: set<string>) returns (prefix': string)
        requires words != {}
        requires t.Valid()
        requires t.words == words
        requires WordRest(prefix, t.words) != {}
        requires IsCommonPrefix(prefix, WordRest(prefix, t.words))
        ensures IsCommonPrefix(prefix', WordRest(prefix, t.words))
        decreases t.repr
        ensures LongestPrefix(prefix', WordRest(prefix, words))
    {
        if |t.children.Keys| == 1 {
            if t.isWord {
                assert "" in t.words;
                assert prefix + "" == prefix;
                assert prefix + "" in WordRest(prefix, t.words);
                assert prefix in WordRest(prefix, t.words);
                longestPrefixIsShortestWord(WordRest(prefix, t.words), prefix);
                return prefix;
            }else{
                var key :| key in t.children.Keys;
                forall w | w in t.words 
                    ensures w[0] == key
                {
                    if w[0] != key {
                        assert w[0] in t.children.Keys;
                        assert |t.children.Keys-{key}| == 0;
                        assert false;
                    }
                }
                assert t.children[key].words == set w | w in t.words :: w[1..];
                assert WordRest(prefix+[key], t.children[key].words) == WordRest(prefix, t.words) by {
                    forall w | w in t.children[key].words
                        ensures prefix + [key] + w in WordRest(prefix, t.words)
                    {
                        assert w in (set tw | tw in t.words :: tw[1..]);
                        var tw :| tw in t.words && tw[1..] == w;
                        assert tw in t.words;
                        assert tw == [key] + w;
                        assert prefix + tw in WordRest(prefix, t.words);
                        assert prefix + tw == prefix + [key] + w;
                        assert prefix +[key] + w in WordRest(prefix, t.words);
                    }
                    forall w | w in WordRest(prefix, t.words)
                        ensures w in WordRest(prefix+[key], t.children[key].words)
                    {
                        var tw :| tw in t.words && prefix + tw == w;
                        assert tw[0] == key;
                        assert tw[1..] in t.children[key].words;
                        assert prefix +[key] + tw[1..] == w;
                        assert w in WordRest(prefix+[key], t.children[key].words);
                    }
                }
                assert t.children[key].words != {};
                prefix' := longestCommonPrefixRec(t.children[key], prefix + [key], t.children[key].words);
                return prefix';
            }
        }
        if |t.children.Keys| == 0 {
            assert t.children.Keys == {};
            assert t.words <= {""} by {
                if w :| w in t.words && w != "" {
                    assert w in t.words;
                    assert w[0] in t.children.Keys;
                    assert false;
                }
            }
            assert t.words != {};
            assert t.words == {""};
            assert prefix + "" == prefix;
            assert prefix in WordRest(prefix, t.words);
            longestPrefixIsShortestWord(WordRest(prefix, t.words), prefix);
            
        }else{
            if "" in t.words {
                assert prefix + "" == prefix;
                assert prefix in WordRest(prefix, t.words);
                longestPrefixIsShortestWord(WordRest(prefix, t.words), prefix);
            }else{
                longestPrefixOfTrieWithMultipleKeys(t, prefix, WordRest(prefix, words));
            }
        }
        return prefix;
    }

}