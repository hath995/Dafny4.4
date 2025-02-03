include "./sets.dfy"
module ImmutableTrie {
    import opened SetCustom

    datatype Trie2 = Trie2(children: map<char, Trie2>, isWord: bool)

    predicate ValidTrie(t: Trie2) 
    {
        t !in t.children.Values &&
        (forall x :: x in t.children.Values ==> ValidTrie(x))
    }

    ghost function ChildrenSet2(parent: Trie2): set<Trie2> 
        decreases parent
    {
        Union(set x | x in parent.children.Values :: ChildrenSet2(x)) + {parent}
    }

    ghost function ChildrenSet(parent: Trie2, children: set<Trie2>, res: set<Trie2>): set<Trie2> 
        requires children <= parent.children.Values
        // requires ValidTrie(parent)
        decreases parent, children
    {
        if children == {} then res else
            var x :| x in children;
            ChildrenSet(parent, children - {x}, res + ChildrenSet(x, x.children.Values, {x}))
    }

    ghost function TrieSet(parent: Trie2): set<Trie2> 
        // requires ValidTrie(parent)
        decreases parent
    {
        ChildrenSet(parent, parent.children.Values, {parent})
    }


    function InsertWord(t: Trie2, word: string): Trie2
        decreases |word|
    {
        if |word| == 0 && t.isWord then
            t
        else if |word| == 0 && !t.isWord then
            Trie2(t.children, true)
        else
            if word[0] in t.children then
                Trie2(t.children[word[0] := InsertWord(t.children[word[0]], word[1..])], t.isWord)
            else
                Trie2(t.children[word[0] := InsertWord(Trie2(map[], false), word[1..])], t.isWord)
    }

    predicate HasWord(t: Trie2, word: string)
        decreases |word|
    {
        if |word| == 0 then
            t.isWord
        else
            if word[0] in t.children then
                HasWord(t.children[word[0]], word[1..])
            else
                false
    }

    function DeleteWord(t: Trie2, word: string): Trie2
        decreases |word|
    {
        if |word| == 0 then
            Trie2(t.children, false)
        else
            if word[0] in t.children then
                var child := DeleteWord(t.children[word[0]], word[1..]);
                // Trie2(t.children[word[0] := DeleteWord(t.children[word[0]], word[1..])], t.isWord)
                Trie2(map key | key in t.children && (
                    (key != word[0] ==> t.children[key].isWord || t.children[key].children.Keys != {}) &&
                    (key == word[0] ==> child.isWord || child.children.Keys != {})
                ):: if key != word[0] then t.children[key] else child, t.isWord)
            else
                t
    }

    lemma ThereIsAMinimum(s: set<char>)
        requires s != {}
        ensures exists x :: x in s && forall y :: y in s ==> x <= y
    {
        assert s != {};
        var x :| x in s;
        if s == {x} {
        } else {
            var s' := s - {x};
            assert s == s' + {x};
            ThereIsAMinimum(s');
        }
    }

    function SetToSequence(s: set<char>): seq<char>
        ensures var q := SetToSequence(s); forall i :: 0 <= i < |q| ==> q[i] in s
        ensures |SetToSequence(s)| == |s|
        ensures forall p :: p in s ==> p in SetToSequence(s)
    {
    if s == {} then [] else
        ThereIsAMinimum(s);
        var x :| x in s && forall y :: y in s ==> x <= y;
        [x] + SetToSequence(s - {x})
    }

    method testTrie2() {
        var t2 := Trie2(map[], false);
        t2 := InsertWord(t2, "hello");
        t2 := InsertWord(t2, "hello!");
        t2 := InsertWord(t2, "boo");
        assert HasWord(t2, "hello");
        assert HasWord(t2, "boo");
        t2 := DeleteWord(t2, "hello");
        assert !HasWord(t2, "hello");
        assert HasWord(t2, "boo");
        assert HasWord(t2, "hello!");
    }

    // function TrieToRegex(t: Trie2): string
    // {
    //     if t.children.Keys == {} then
    //         ""
    //     else
    //         var children := SetToSequence(t.children.Keys);
    //         assert forall c :: c in children ==> c in t.children.Keys;
    //         var pairs := Map((c: char) requires c in t.children.Keys => (c, TrieToRegex(t.children[c])), children);
    //         var ss := Map((p: (char, string)) => [p.0] + if p.1 != "" && Contains(p.1, "|") then "("+p.1+")" else p.1, pairs);
    //         var s := sumSeq(ss, "|");
    //         s + if t.isWord then "|" else ""
    // }
}