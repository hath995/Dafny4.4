

module Tries {
    datatype Trie2 = Trie2(children: map<char, Trie2>, isWord: bool)
    ghost function Union<T>(s: set<set<T>>): set<T> 
    {
        if s == {} then 
            assert forall x :: x in s ==> x <= {};
            {} 
        else
            var x :| x in s;
            assert forall x :: x in s ==> x <= x + Union(s - {x});
            x + Union(s - {x})
    }


    lemma UnionPlusSuperset<T>(s: set<set<T>>, x: set<T>, y: set<T>)
        requires x <= y
        requires x in s
        requires forall y :: y in s ==> y != {}
        ensures Union(s)+y == Union(s-{x} + {y})
        decreases s
    {
        if s == {} {

        }else{
            UnionPlusOne(s-{x}, x);
            calc{
                Union(s-{x}+{x});
                Union(s-{x}) + x;
                {assert s-{x}+{x} == s;} 
                Union(s);
            }
            // calc {
            //     Union(s-{x}+{y});
            //     {UnionPlusOne(s-{x}, y);}
            //     Union(s-{x}) + y;
            //     Union(s-{x}) + y + x;
            //     // Union(s-{x} + {y}) + y;
            //     Union(s) + y;
            // }
            assert Union(s-{x}+{x}) == Union(s-{x}) + x;
            assert Union(s) == Union(s-{x}) + x;
            assert Union(s) + y == Union(s-{x}) + x + y;
            assert Union(s-{x}) + y == Union(s-{x}) + x + y;
            UnionPlusOneIdempotent(s-{x}, y);

        }
    }

    lemma UnionPlusOneIdempotent<T>(s: set<set<T>>, x: set<T>)
        requires x != {}
        requires forall y :: y in s ==> y != {}
        ensures Union(s + {x}) == Union(s) + x
        decreases s
    {
        if s == {} {
        } else if x !in s {
            UnionPlusOne(s, x);
        }else{
            assert s+{x} == s;
            assert Union(s+{x}) == Union(s);
            UnionHasAll(s);
        }
    }
    lemma UnionPlusOne<T>(s: set<set<T>>, x: set<T>)
        requires x != {}
        requires forall y :: y in s ==> y != {}
        requires x !in s
        ensures Union(s + {x}) == Union(s) + x
        decreases s
    {
        if s == {} {
            assert Union({x}) == x;
            assert Union(s + {x}) == Union({x});
            assert Union(s) == {};
            assert Union(s) + x == x;
        } else {
            // var y :| y in s && Union(s) == y + Union(s - {y});
            // // UnionPlusOne(s - {y}, y);
            // // assert Union((s-{y})+{y}) == Union(s - {y}) + y;
            // UnionPlusOne(s - {y}, x);
            // assert Union(s - {y} + {x}) == Union(s - {y}) + x;
            assert s+{x} != {};
            var z :| z in s + {x} && Union(s+{x}) == z + Union((s+{x})- {z} );
            if z == x {

            }else {
                assert Union(s+{x}) == z + Union(s+{x} - {z});
                UnionPlusOne(s-{z}, x);
                assert Union(s-{z}+{x}) == Union(s-{z}) + x;
                assert s -{z} + {x} == s+{x}-{z};
                UnionPlusOne(s-{z}, z);
                // assert Union(s-{z}+{z}) == Union(s-{z}) + z;
                assert s -{z} + {z} == s ;
                assert Union(s) == Union(s-{z}) + z;
                assert Union(s-{z}+{x}) == Union(s-{z}) + x;
                // assert Union(s+{x}) == Union(s-{z}) + z;
                calc {
                    Union(s+{x});
                    z + Union(s+ {x}-{z});
                    Union(s+ {x}-{z})+z;
                    Union(s-{z})+x+z;
                    Union(s-{z})+z+x;
                }

            }
            // assert Union(s + {x}) == Union(s - {y} + {x}) == Union(s - {y}) + x;
            // assert Union(s + {x}) == Union(s + {x - {y}}) + y;
            // assert Union(s + {x - {y}}) == Union(s) + x - {y};
            // assert Union(s + {x}) == Union(s) + x;
        }
    }

    lemma UnionContains<T>(s: set<set<T>>, x: T)
        requires x in Union(s)
        ensures exists y :: y in s && x in y
    {
    }
    
    lemma UnionHasAll<T>(s: set<set<T>>)
        ensures forall x :: x in s ==> x <= Union(s)
        ensures forall y :: y in s ==> forall x :: x in y ==> x in Union(s)
    {
        if s == {} {
            assert forall x :: x in s ==> x <= Union(s);
        } else {
            var x :| x in s && Union(s) == x + Union(s - {x});
            UnionHasAll(s - {x});
            // assert forall x :: x in s-{x} ==> x <= Union(s-{x});
            // assert x <= x + Union(s-{x});
            forall y | y in s
                ensures y <= x + Union(s-{x}) 
            {
                if y == x {
                    assert y <= x;
                } else {
                    assert y in s-{x};
                    assert y <= Union(s-{x});
                    assert y <= x + Union(s-{x});
                }
            }
            // assert Union(s) == x + Union(s-{x});
            // assert forall x :: x in s ==> x <= Union(s);
        }
    }

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

    class Trie {
        var children: map<char, Trie>
        var isWord: bool
        ghost var repr: set<Trie>
        ghost var words: set<string>

        constructor() 
            ensures fresh(this.repr)
            ensures this.isWord == false
            ensures this.children.Keys == {}
            ensures this.children.Values == {}
            ensures this.words == {}
            ensures Valid()
            ensures ValidWords()
        {
            children := map[];
            isWord := false;
            words := {};
            new;
            assert this !in this.children.Values;
            repr := {this};
        }

        ghost function ChildUnion() : set<Trie> 
            reads this`children, this.children.Values
            decreases repr
        {
            Union(set x | x in children.Values :: x.repr)+ this.children.Values
        }

        predicate has(word: string)
            requires Valid()
            reads this, repr
            decreases repr
        {
            if |word| > 0 then 
                if word[0] in children then 
                    children[word[0]].has(word[1..])
                else 
                    false
            else
                isWord
        } 

        twostate lemma ChildUnionContains(root: Trie, child: Trie)
            requires old(root.Valid())
            // requires root2.Valid()
            requires child.Valid()
            requires forall x :: x in old(root.children.Values) ==> unchanged(x)
            requires forall x :: x in old(root.children.Values) ==> x.repr !! child.repr
            requires child !in old(root.children.Values)
            requires root.children.Values == old(root.children.Values)+{child}
            ensures root.ChildUnion() == old(root.ChildUnion()) + child.repr
        {
                assert child !in old(root.children.Values);
                assert root.children.Values == old(root.children.Values) + {child};
                assert forall x :: x in old(root.children.Values) ==> old(x.Valid()) && old(x.repr) != {};
                ghost var olds := set x | x in old(root.children.Values) :: old(x.repr);
                assert forall x :: x in olds ==> x != {};
                assert forall x ::x in old(root.children.Values) ==> x.repr == old(x.repr);
                assert (set x | x in old(root.children.Values) :: x.repr) == olds; 
                UnionPlusOne(set x | x in old(root.children.Values) :: x.repr, child.repr);
                assert root.children.Values == old(root.children.Values) + {child};
                assert (set x | x in root.children.Values :: x.repr) == set x | x in (old(root.children.Values)+{child}) :: x.repr;
                assert (set x | x in (old(root.children.Values)+{child}) :: x.repr) == (set x | x in old(root.children.Values) :: x.repr) + {child.repr};
                calc {
                    Union(set x | x in root.children.Values :: x.repr);
                    Union(set x | x in (old(root.children.Values)+{child}) :: x.repr);
                    Union((set x | x in old(root.children.Values) :: x.repr) + {child.repr});
                    Union(set x | x in old(root.children.Values) :: x.repr) + child.repr;
                }
                assert child in child.repr;
                assert child.repr + {child} == child.repr;
                calc {
                    root.ChildUnion();
                    Union(set x | x in root.children.Values :: x.repr) + root.children.Values;
                    Union(set x | x in root.children.Values :: x.repr) + old(root.children.Values) + {child};
                    Union(set x | x in old(root.children.Values) :: x.repr) + child.repr + old(root.children.Values) + {child};
                    Union(set x | x in old(root.children.Values) :: x.repr) + old(root.children.Values) + child.repr + {child};
                    Union(set x | x in old(root.children.Values) :: x.repr) + old(root.children.Values) + child.repr;
                    Union(set x | x in old(root.children.Values) :: old(x.repr)) + old(root.children.Values) + child.repr;
                    old(root.ChildUnion()) + child.repr;
                }
                // assert child in root.ChildUnion();
                // assert child in old(root.ChildUnion()) + {child};
            // }
        }

        ghost predicate Valid() 
            reads this, repr
            // ensures Valid() ==> this in repr //for export of opaque functions
            decreases repr
        {
            this in this.repr &&
            (
                forall x <- this.children.Keys :: (
                    this.children[x] in this.repr &&
                    this.children[x].repr <= this.repr &&
                    this !in this.children[x].repr && 
                    this.children[x].Valid()
                )
            ) &&
            (forall x <- this.children.Keys, y <- this.children.Keys :: x != y ==> this.children[x] != this.children[y]) &&
            (forall x <- this.children.Keys, y <- this.children.Keys :: this.children[x] != this.children[y] ==> this.children[x].repr !! this.children[y].repr) &&
            (this.children.Keys == {} ==> this.repr == {this}) &&
            (this.children.Keys != {} ==> this.repr == {this}+Union(set k | k in this.children.Keys :: this.children[k].repr)) &&
            (forall word :: word in this.words && |word| > 0 ==> word[0] in this.children.Keys)
        }

        ghost predicate ValidWords()
            requires Valid()
            reads this, repr
            decreases repr
        {
            (forall word :: word in this.words ==> this.has(word))  &&
            (forall key :: key in this.children.Keys ==> this.children[key].words == set ws | ws in this.words && |ws| > 0 && ws[0] == key :: ws[1..]) &&
            (forall key :: key in this.children.Keys ==> this.children[key].ValidWords()) &&
            // required for TrieDoesNotHaveWord
            ("" in this.words <==> this.isWord)
        }

        lemma TrieDoesNotHaveWord( word: string)
            requires Valid()
            requires ValidWords()
            requires word !in this.words
            ensures this.has(word) == false
            decreases this.repr
        {
            if |word| > 0 {
                if word[0] in this.children {
                    assert word[1..] !in this.children[word[0]].words by {
                        if word[1..] in this.children[word[0]].words {
                            assert word[1..] in this.children[word[0]].words;
                            assert word[1..] in set ws | ws in this.words && |ws| > 0 && ws[0] == word[0] :: ws[1..];
                            var w :| w in this.words && |w| >0 && w[0] == word[0] && w[1..] == word[1..];
                            assert w == word;
                            assert false;
                        }
                    }
                    this.children[word[0]].TrieDoesNotHaveWord( word[1..]);
                } else {
                    assert word[0] !in this.children.Keys;
                    assert this.has(word) == false;
                }
            } else {
                assert this.isWord == false;
                assert this.has(word) == false;
            }
        }

        lemma WordsNotInWordsTrieDoesNotHave()
            requires Valid()
            requires ValidWords()
            ensures forall word :: word !in this.words ==> this.has(word) == false
            decreases this.repr
        {
            forall word | word !in this.words
                ensures this.has(word) == false
            {
                TrieDoesNotHaveWord(word);
            }
        }

        method {:verify } {:vcs_split_on_every_assert} insertRecursive(word: string)// returns (child': Trie)
            requires this.Valid()
            requires ValidWords()
            ensures this.Valid()
            ensures ValidWords()
            ensures this.words == old(this.words) + {word}
            ensures this.repr >= old(this.repr)
            ensures fresh(this.repr - old(this.repr))
            ensures |word| == 0 ==> this.isWord
            // ensures |word| > 0 ==> forall x :: x in this.children.Keys && x != word[0] ==> this.children[x].repr <= old(repr) && unchanged(this.children[x].repr)
            ensures |word| >0 ==> word[0] in this.children.Keys
            modifies repr
        {
            if |word| > 0 {
                if word[0] in this.children {
                    this.children[word[0]].insertRecursive(word[1..]);
                    this.words := this.words + {word};
                    this.repr := this.repr + this.children[word[0]].repr;
                    calc {
                     (set x | x in this.children.Keys :: this.children[x].repr);
                     (set x | x in this.children.Keys && x != word[0] :: old(this.children[x].repr)) + {this.children[word[0]].repr};
                     (set x | x in this.children.Keys :: old(this.children[x].repr))-{old(this.children[word[0]].repr)} + {this.children[word[0]].repr};
                    }
                    UnionPlusSuperset(set x | x in this.children.Keys :: old(this.children[x].repr), old(this.children[word[0]].repr), this.children[word[0]].repr);
                } else {
                    var child := new Trie();
                    assert child.words == {};
                    child.insertRecursive(word[1..]);
                    this.children := this.children[word[0] := child];
                    this.words := this.words + {word};
                    this.repr := this.repr + child.repr;
                    assert this.children.Keys == old(this.children.Keys) + {word[0]};
                    assert fresh(child.repr);
                    assert this.children[word[0]] == child;
                    assert forall x :: x in this.children.Keys && x != word[0] ==> this.children[x].repr !! child.repr;
                    assert forall x,y :: x in this.children.Keys && y in this.children.Keys && x != y ==> this.children[x] != this.children[y];
                    assert (set x | x in this.children.Keys && x != word[0] :: this.children[x].repr) == set x | x in this.children.Keys && x != word[0] :: old(this.children[x].repr);
                    calc {
                        this.repr;
                        Union(set x | x in old(this.children.Keys) :: old(this.children[x].repr)) + child.repr + {this};
                        {assert (set x | x in old(this.children.Keys) :: old(this.children[x].repr)) == (set x | x in this.children.Keys && x != word[0] :: this.children[x].repr);}    
                        Union(set x | x in this.children.Keys && x != word[0] :: this.children[x].repr) + child.repr+ {this};
                        {UnionPlusOne(set x | x in this.children.Keys && x != word[0] :: (this.children[x].repr), child.repr);}
                        Union((set x | x in this.children.Keys && x != word[0] :: this.children[x].repr) + {child.repr}) + {this};
                        {assert (set x | x in this.children.Keys && x != word[0] :: this.children[x].repr) + {child.repr} == set x | x in this.children.Keys :: this.children[x].repr;}
                        Union(set x | x in this.children.Keys :: this.children[x].repr)+ {this};
                    }
                    // assert this.repr == {this} + Union(set x | x in this.children.Keys :: this.children[x].repr);
                    // assert Valid();
                    // assert ValidWords();
                }
            }else{
                this.isWord := true;
                this.words := this.words + {word};
                assert (set x | x in this.children.Keys :: this.children[x].repr) == (set x | x in this.children.Keys :: old(this.children[x].repr));
                assert Valid();
                assert ValidWords();
            }
        }

        lemma ValidImpliesAllValid(root: Trie)
            requires root.Valid()
            ensures forall x :: x in root.repr ==> x.Valid()
            decreases root.repr
        {
            if root.children.Keys == {} {

            }else {
                forall node | node in root.repr
                    ensures node.Valid()
                {
                    if node == root {
                        assert root.Valid();
                    } else if node in root.children.Values {
                        assert node.Valid();
                    } else {
                        assert node !in root.children.Values;
                        // assert node in Union(set x | x in root.children.Values :: x.repr);
                        UnionContains(set x | x in root.children.Keys :: root.children[x].repr, node);
                        var k :| k in root.children.Keys && node in root.children[k].repr;
                        ValidImpliesAllValid(root.children[k]); 
                        assert node.Valid();
                    }
                }
            }
        }
        lemma {:verify } AllChildrenInRepr(root: Trie, child: Trie)
            requires root.Valid()
            requires child in root.repr
            ensures child.repr <= root.repr
            decreases root.repr
        {
            if root.children.Keys == {} {
                assert root.repr == {root} by {
                    assert root in root.repr;
                    var x :| x in root.repr ;
                    if x != root {
                        // var k :| k in root.children.Keys && root.children[k] == x;
                        assert x !in root.repr;
                        assert false;
                    }
                }
                assert child == root;
                assert child.children.Values < root.repr;
            } else {
                if child == root {}
                else if child in root.children.Values {
                    assert child in root.children.Values;
                    assert child.children.Values < root.repr;
                } else {
                    UnionContains(set x | x in root.children.Keys :: root.children[x].repr, child);
                    var k :| k in root.children.Keys && child in root.children[k].repr;
                    // assert child in Union(set x | x in root.children.Values :: x.repr);
                    // UnionContains(set x | x in root.children.Values :: x.repr, child);
                    // var x :| x in root.children.Values && child in x.repr;
                }
            }
        }

        twostate lemma {:verify false} CurrentChildrenNotInSpineSet(root: Trie, current: Trie, spine: seq<Trie>, spineSet: set<Trie>, reprSpine: set<Trie>, added: set<Trie>)
            requires old(root.Valid())
            requires root.Valid()
            requires current.Valid()
            requires |spine| > 0
            requires forall x :: x in spine ==> x.Valid()
            requires forall x :: x in spine ==> x in spineSet
            requires forall x :: x in spineSet ==> x in spine
            requires current == spine[|spine| - 1]
            requires |spine| > 0 ==> spine[0] == root
            requires forall i :: 1 <= i < |spine| ==> spine[i] in spine[i-1].children.Values
            requires forall i,j :: 0 <= i < j < |spine| ==> spine[j].repr < spine[i].repr
            requires current in old(root.repr)+added
            requires forall x :: x in spineSet ==> x in old(root.repr) + added
            requires added !! old(root.repr)
            requires forall x :: x in reprSpine ==> x in old(root.repr)
            requires spineSet == reprSpine + added
            requires old(root.repr) <= root.repr
            requires current in old(root.repr) ==> added == {}
            requires current in old(root.repr) ==> forall node :: node in old(root.repr) ==> unchanged(node)
            ensures current.children.Values !! spineSet
            decreases root.repr
        {
            if current == root {
                assert root in root.repr;
                assert root in old(root.repr);
                assert added == {};
                assert spine == [root];
                assert spineSet == {root};
                assert reprSpine == {root}; 
            }else{

            }
        }

        twostate lemma {:verify false}  UpdatedCurrentValid(current: Trie, child: Trie, updates: map<char, Trie>, c: char)
            requires allocated(current)
            requires old(current.Valid())
            requires child.children.Values == {}
            requires child.Valid()
            requires child !in old(current.repr)
            requires c !in old(current.children.Keys)
            requires updates == old(current.children)[c := child]
            requires forall node :: node in old(current.ChildUnion()) ==> unchanged(node)
            requires current.children == updates
            requires current.repr == old(current.repr) + {child}
            ensures current.Valid()
        {
            assert c in current.children.Keys;
            assert child in current.children.Values;
            assert current.children.Values != {};
            assert forall x,y :: x in current.children.Values && y in current.children.Values && x != y ==> x.repr !! y.repr by {
                forall x,y | x in current.children.Values && y in current.children.Values && x != y
                    ensures x.repr !! y.repr
                {
                    if x == child  {
                        assert x.repr !! y.repr;
                    } else if y == child {
                        assert y.repr == {child};
                        assert x in old(current.repr);
                        assert x.repr !! y.repr;
                    } else {
                        assert x in old(current.repr);
                        assert y in old(current.repr);
                        assert x.repr !! y.repr;
                    }
                }
            }
            assert forall k :: k in old(current.children.Keys) ==> k in current.children.Keys && current.children[k] == old(current.children[k]);
            assert forall x :: x in old(current.children.Values) ==> unchanged(x);
            assert forall x :: x in old(current.children.Values) ==> x.repr !! child.repr;
            // assert old(current.children.Values) < current.children.Values;
            assert current.children.Values == old(current.children.Values) + {child};
            ChildUnionContains(current, child);
            assert current.ChildUnion() == old(current.ChildUnion()) + child.repr;
            assert current.ChildUnion() == old(current.ChildUnion()) + {child};
            assert current.repr == {current}+current.ChildUnion();
            assert current !in current.ChildUnion();
            assert current.children.Values < current.repr;
            assert forall xs :: xs in current.children.Values ==> xs.repr <= current.ChildUnion() && xs.Valid() by {
                forall xs | xs in current.children.Values
                    ensures xs.repr <= current.ChildUnion() && xs.Valid()
                {
                    if xs == child {
                        assert xs.repr == child.repr;
                        assert current !in current.ChildUnion();
                        assert xs.Valid();
                        assert xs.repr <= current.ChildUnion();
                    } else {
                        assert xs in old(current.repr);
                        assert xs.repr < current.ChildUnion();
                        assert xs.Valid();
                    }
                }
            }
        }

        lemma SpineRepr(root: Trie, spine: seq<Trie>)
            requires root.Valid()
            requires |spine| > 0
            requires spine[0] == root
            requires forall x :: x in spine ==> x.Valid()
            requires forall i :: 1 <= i < |spine| ==> spine[i] in spine[i-1].children.Values
            ensures forall i,j :: 0 <= i < j < |spine| ==> spine[j].repr < spine[i].repr
            decreases |spine|
        {
            if |spine| == 1 {

            }else{
                SpineRepr(root, spine[..|spine|-1]);
                forall i,j | 0 <= i < j < |spine|
                    ensures spine[j].repr < spine[i].repr
                {
                    if 1 <= i < j < |spine| -1 {

                        assert spine[j].repr < spine[i].repr;
                    }else{
                        forall i | 0 <= i < |spine| - 1
                            ensures spine[|spine| - 1].repr < spine[i].repr
                        {
                            if i == |spine| - 2 && 0 <= i < |spine| - 1 {
                                assert spine[|spine| - 1] in spine[i].children.Values;
                                AllChildrenInRepr(spine[i], spine[|spine| - 1]);
                                // assert spine[|spine| - 1].repr <= spine[i].ChildUnion();
                                assert spine[|spine| - 1].repr < spine[i].repr;
                            }else{
                                assert |spine| > 2;
                                assert i < |spine| - 2;
                                assert spine[|spine|-2].repr < spine[i].repr;
                                AllChildrenInRepr(spine[|spine|-2], spine[|spine| - 1]);
                                assert spine[|spine| - 1].repr < spine[i].repr;
                            }
                        }

                    }
                }
            }
        }

        lemma SpineSetDistinct(spine: seq<Trie>, spineSet: set<Trie>)
            requires |spine| > 0
            requires forall x :: x in spine ==> x.Valid()
            requires forall x :: x in spine ==> x in spineSet
            requires forall x :: x in spineSet ==> x in spine
            requires forall i :: 1 <= i < |spine| ==> spine[i] in spine[i-1].children.Values
            ensures forall i,j :: 0 <= i < j < |spine| ==> spine[j] != spine[i]
            decreases |spine|
        {
            if |spine| <= 1 {

            }else{
                assert spine == [spine[0]] + spine[1..];
                SpineRepr(spine[0], spine);
                SpineSetDistinct(spine[1..], spineSet-{spine[0]});
            }
        }

        lemma {:verify false} currentChildUnionNotInSpineSet(root: Trie, current: Trie, spine: seq<Trie>, spineSet: set<Trie>)
            requires current.Valid()
            requires |spine| > 0
            requires forall x :: x in spine ==> x.Valid()
            requires forall x :: x in spine ==> x in spineSet
            requires forall x :: x in spineSet ==> x in spine
            requires current == spine[|spine| - 1]
            requires |spine| > 0 ==> spine[0] == root
            requires forall i :: 1 <= i < |spine| ==> spine[i] in spine[i-1].children.Values
            ensures current.children.Values !! spineSet
            ensures current.ChildUnion() !! spineSet
            decreases root.repr
        {
            if |spine| == 1 {
                assert current == root;
                assert current !in current.ChildUnion();
                assert current.children.Values < current.repr;
                assert current.children.Values <= current.ChildUnion();
                assert current.children.Values !! spineSet;
                assert current.ChildUnion() !! spineSet;
            }else{
                SpineSetDistinct(spine, spineSet);
                SpineRepr(spine[0], spine);
                assert current != root;
                currentChildUnionNotInSpineSet(spine[1], current, spine[1..], spineSet-{root});
            }
        }

        // twostate lemma {:verify false} FixupSpineset(spine: seq<Trie>, spineSet: set<Trie>, current: Trie, k: int, child: Trie)
        //     requires |spine| > 0
        //     requires child.Valid()
        //     requires child.children.Values == {}
        //     requires old(current.Valid())
        //     requires current.children.Values == old(current.children.Values) + {child}
        //     requires current.repr == old(current.repr) + child.repr
        //     requires child in current.repr
        //     requires current.Valid()
        //     requires forall i :: 1 <= i < |spine| ==> spine[i] in spine[i-1].children.Values
        //     requires forall i,j :: 0 <= i < j < |spine| ==> spine[j].repr < spine[i].repr
        //     requires forall i :: 0 <= i < |spine| ==> old(spine[i].Valid())
        //     requires forall x :: x in spine ==> x in spineSet
        //     requires forall x :: x in spineSet ==> x in spine
        //     requires 0 <= k < |spine|
        //     requires forall i :: 0 <= i < |spine|-1 ==> child !in old(spine[i].repr)
        //     requires forall i :: 0 <= i < |spine|-1 ==> child.repr !! old(spine[i].repr)
        //     requires forall node :: node in spine[(k+1)..] ==> node.Valid()
        //     requires forall node :: node in spine[k..] ==> node.repr == old(node.repr) + child.repr
        //     requires forall node :: node in spine[k..] ==> node.children.Values == old(node.children.Values)
        //     requires current.children.Values !! spineSet
        //     requires current == spine[|spine| - 1] 
        //     ensures forall node :: node in spine[k..] ==> node.Valid()
        // {
        //     if k == |spine| - 1 {
        //         assert spine[k] == current;
        //         assert child in current.repr;
        //         assert child in spine[k].repr;
        //         assert spine[k].Valid();
        //         assert forall node :: node in spine[k..] ==> node.Valid();
        //     } else {
        //         assert spine[k].repr == old(spine[k].repr) + {child};
        //         assert spine[k].Valid() by {
        //             assert spine[k] in spine[k].repr;
        //             assert spine[k] !in spine[k].children.Values;
        //             assert spine[k].children.Values != {};
        //             assert spine[k].children.Values < spine[k].repr;
        //             // assert forall x :: x in spine[k].children.Values ==> x.repr !! child.repr; 
        //             assert forall node :: node in spine[(k+1)..] ==> node.ChildUnion() == old(spine[j].ChildUnion()) + child.repr;
        //             assert spine[k] !in spine[k].ChildUnion();
        //             assert spine[k].repr == {spine[k]}+ spine[k].ChildUnion();
        //         }
        //         assert forall node :: node in spine[k..] ==> node.Valid();
        //         // FixupSpineset(spine, spineSet, current, k-1, child);
        //         // assert spine[k].repr == old(spine[k].repr) + {child};
        //         // assert child in spine[k].repr;
        //         // assert spine[k].Valid();
        //     }
        // }

        method {:verify false}  insertBare(word: string)
            requires this.Valid()
            ensures this.Valid()
            modifies this, repr, children.Values, ChildUnion()
        {
            var current := this;
            ghost var spine: seq<Trie> := [this];
            for i := 0 to |word| 
                invariant old(this.repr) <= this.repr
                invariant current.children.Values < repr
                invariant current.Valid()
                invariant this.Valid()
                modifies repr
            {
                if word[i] in current.children {
                    var childTrie := current.children[word[i]];
                    current := current.children[word[i]];
                } else {
                    var child := new Trie();
                    var updatedChildren := current.children[word[i] := child];
                    current.repr := current.repr + {child};

                    var k := |spine| - 1;
                    ghost var rechanged: set<Trie> := {};
                    while k >= 0
                        invariant -1 <= k < |spine|
                        invariant forall i :: 1 <= i < |spine| ==> spine[i] in spine[i-1].children.Values
                        invariant forall x :: x in spine[(k+1)..] ==> x.repr == old(x.repr)+{child}
                        invariant forall x :: x in spine[(k+1)..] ==> x.Valid()
                    {
                        if k == |spine| -1 {
                            assert spine[k] == current;
                            assert child in current.repr;
                            assert spine[k].Valid();
                            rechanged := rechanged + {spine[k]};
                        } else {
                            rechanged := rechanged + {spine[k]};
                            spine[k].repr := spine[k].repr + {child};
                            assert spine[k].Valid();
                        }
                       k := k - 1;
                    }
                    current := child;
                }
            }
            current.isWord := true;
        }

        method {:verify false} {:vcs_split_on_every_assert} insert(word: string)
            requires this.Valid()
            ensures this.Valid()
            modifies this, repr, children.Values, ChildUnion()
        {
            var current := this;
            // ghost var allTries := this.repr;
            ghost var spine: seq<Trie> := [this];
            ghost var spineSet: set<Trie> := {this};
            ghost var reprSpine: set<Trie> := {this};
            assert this.ChildUnion() < this.repr;
            ValidImpliesAllValid(this);
            // assert children.Values < allTries;
            ghost var added: set<Trie> := {};
            assert forall x :: x in repr ==> allocated(x);
            label LoopStart:
            for i := 0 to |word| 
                invariant repr == old(repr) + added
                invariant forall y :: y in added ==> fresh(y)
                invariant forall x :: x in added ==> x.repr < repr
                invariant forall x :: x in reprSpine ==> x in old(repr)
                invariant spineSet == reprSpine + added
                invariant reprSpine !! added
                invariant |spine| > 0
                invariant forall x :: x in spine ==> x in repr
                invariant current == spine[|spine| - 1]
                invariant |spine| > 0 ==> spine[0] == this
                invariant forall i :: 1 <= i < |spine| ==> spine[i] in spine[i-1].children.Values
                invariant forall i,j :: 0 <= i < j < |spine| ==> spine[j].repr < spine[i].repr
                invariant forall x :: x in spine ==> x in spineSet
                invariant forall x :: x in spineSet ==> x in spine
                invariant repr - spineSet <= repr
                invariant forall x :: x in (repr - spineSet) ==> (x in old(this.repr) && unchanged(x))
                invariant old(this.repr) <= this.repr
                // invariant current in old(this.repr) ==> added == {}
                // invariant current in old(this.repr) ==> forall node :: node in old(this.repr) ==> unchanged(node)
                invariant current.children.Values < repr
                invariant current.children.Values !! spineSet
                invariant current.Valid()
                invariant this.Valid()
                invariant forall node :: node in repr ==> node.Valid()
                modifies repr
            {
                if word[i] in current.children {
                    // assert current in allTries;
                    assert word[i] in current.children.Keys;
                    var childTrie := current.children[word[i]];
                    if childTrie in repr {
                    assert childTrie in current.children.Values;
                    AllChildrenInRepr(this, childTrie);
                    // assert current.children[word[i]].repr  <= allTries;
                    } else {
                        assert childTrie in added;
                        assert childTrie !in repr;
                        assert childTrie in current.children.Values;
                        // assert current.children[word[i]].repr  < allTries;
                    }
                    current := current.children[word[i]];
                    spine := spine + [current];
                    spineSet := spineSet + {current};
                    if current !in added {
                        reprSpine := reprSpine + {current};
                    }
                    SpineRepr(this, spine);
                    // assert current.children.Values < allTries;
                    // assert forall x :: x in allTries ==> x.Valid();
                    // CurrentChildrenNotInSpineSet(this, current, spine, spineSet, reprSpine, added);
                } else {
                    var child := new Trie();
                    added := added + {child};
                    label BeforeUpdate:
                    ghost var oldc := current.children;
                    var updatedChildren := current.children[word[i] := child];
                    assert updatedChildren[word[i]] == child;
                    assert child in updatedChildren.Values;
                    currentChildUnionNotInSpineSet(this, current, spine, spineSet);
                    current.children := updatedChildren;
                    if oldc.Values == {} {
                        assert current.children.Values == {child};
                    } else {
                        assert child !in oldc.Values;
                        assert forall k :: k in oldc.Keys ==> k in current.children.Keys && current.children[k] == oldc[k];
                        assert forall x :: x in oldc.Values ==> x in current.children.Values;
                        assert current.children.Values == oldc.Values+{child};
                    }
                    // assert current.children.Values < allTries;
                    current.repr := current.repr + {child};
                    UpdatedCurrentValid@BeforeUpdate(current, child, updatedChildren, word[i]);
                    assert current.repr == old@BeforeUpdate(current.repr) + {child};
                    assert child in current.repr;
                    assert current.Valid();
                    // currentChildUnionNotInSpineSet@BeforeUpdate(this, current, spine, spineSet, child);
                    // currentChildUnionNotInSpineSet(this, current, spine, spineSet);
                    assert spineSet * current.repr == {current};
                    // label AfterUpdate:
                    // ghost var allTheRest := repr - spineSet - current.ChildUnion();
                    // ghost var unchangedChildren: set<Trie> := current.ChildUnion() - {child};
                    // assert forall x :: x in unchangedChildren ==> unchanged@BeforeUpdate(x);
                    // var k := |spine| - 1;
                    // ghost var rechanged: set<Trie> := {};
                    // while k >= 0
                    //     invariant -1 <= k < |spine|
                    //     invariant spine[|spine|-1] == current
                    //     // invariant current.repr !! 
                    //     invariant rechanged <= spineSet
                    //     invariant forall x :: x in spine[(k+1)..] ==> x in rechanged
                    //     invariant forall i :: 1 <= i < |spine| ==> spine[i] in spine[i-1].children.Values
                    //     invariant k == |spine| - 1 ==> unchangedChildren == current.ChildUnion()-{child}
                    //     invariant k < |spine| - 1 ==> unchangedChildren == spine[k+1].ChildUnion()-{child}
                    //     invariant unchanged@AfterUpdate(allTheRest)
                    //     invariant unchanged@AfterUpdate(unchangedChildren)
                    //     invariant allTheRest !! unchangedChildren
                    //     invariant allTheRest + unchangedChildren == repr - spineSet - {child}
                    //     // invariant forall node :: node in old@BeforeUpdate(repr) - spineSet ==> unchanged@BeforeUpdate(node)
                    //     invariant forall x :: x in spine[(k+1)..] ==> x.repr == old@BeforeUpdate(x.repr)+{child}
                    //     invariant forall x :: x in spine[(k+1)..] ==> x.Valid()
                    //     // invariant forall x :: x in (repr - spineSet) ==> (x in old@AfterUpdate(this.repr) && unchanged@AfterUpdate(x))
                    // {
                    //     if k == |spine| -1 {
                    //         assert spine[k] == current;
                    //         assert child in current.repr;
                    //         assert child in spine[k].repr;
                    //         assert spine[k].Valid();
                    //         rechanged := rechanged + {spine[k]};
                    //     } else {
                    //         rechanged := rechanged + {spine[k]};
                    //         spine[k].repr := spine[k].repr + {child};
                    //         allTheRest := allTheRest - (spine[k].ChildUnion()-spine[k+1].repr);
                    //         unchangedChildren := unchangedChildren + spine[k].ChildUnion()-spine[k+1].repr;
                    //         assert spine[k].Valid();
                    //     }
                    //    k := k - 1;
                    // }
                    assert spine[0] == this;
                    assert spine[0].Valid();
                    ValidImpliesAllValid(this);
                    current := child;
                    spine := spine + [current];
                    spineSet := spineSet + {current};
                    if current in old(repr) {
                        reprSpine := reprSpine + {current};
                    }
                    assert child in spine[|spine|-2].children.Values;
                    SpineRepr(this, spine);
                    // CurrentChildrenNotInSpineSet(this, current, spine, spineSet, reprSpine, added);
                }
            }
            // assert current in allTries;
            current.isWord := true;
        }

        method Test() {
            var trie := new Trie();
            trie.insertRecursive("hello");
            trie.insertRecursive("boo");
            assert trie.has("hello");
            assert trie.has("boo");
            trie.WordsNotInWordsTrieDoesNotHave();
            assert !trie.has("book");
            assert !trie.has("foobar");
        }
    }
}