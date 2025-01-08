

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
        if |word| == 0 then
            t
         else if |word| == 1 then
            if word[0] in t.children && t.children[word[0]].isWord then
                t
            else 
                Trie2(t.children[word[0] := Trie2(map[], true)], t.isWord)
         else
            if word[0] in t.children then
                Trie2(t.children[word[0] := InsertWord(t.children[word[0]], word[1..])], t.isWord)
            else
                Trie2(t.children[word[0] := InsertWord(Trie2(map[], false), word[1..])], t.isWord)
            // var child := new Trie();
            // children := children[word[0] := child];
            // return child.insert(word[1..]);
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

        constructor() 
            ensures fresh(this)
            ensures this.isWord == false
            ensures this.children.Keys == {}
            ensures this.children.Values == {}
            ensures Valid()
        {
            children := map[];
            isWord := false;
            new;
            assert this !in this.children.Values;
            repr := {this};
            // assert TrieSet(this) == {this};
        }

        ghost function ChildUnion() : set<Trie> 
            reads this, children.Values
            decreases repr
        {
            Union(set x | x in children.Values :: x.repr)+ this.children.Values
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
            decreases repr
        {
            this in this.repr &&
            this !in this.children.Values &&
            (this.children.Values == {} ==> this.repr == {this} && this.children.Values < this.repr) &&
            (this.children.Values != {} ==> (
                this.children.Values < this.repr &&
                this.repr == {this}+ChildUnion() && 
                this !in ChildUnion() &&
                (forall x,y :: x in this.children.Values && y in this.children.Values && x != y ==> x.repr !! y.repr) &&
                (
                    forall x :: x in this.children.Values ==> (
                        // x in repr &&
                        // x.repr < repr && 
                        // x.children.Values < ChildUnion() &&
                        // x.children.Values < x.repr &&
                        // this !in x.repr && 
                        x.repr <= ChildUnion() &&
                        x.Valid()
                    ))
                // UnionHasAll(set x | x in children.Values :: x.repr);
                // ChildUnion() < repr &&
                // this.children.Values < ChildUnion() &&
                // this.children.Values < this.repr &&
                )
            )
        }

        lemma ValidImpliesAllValid(root: Trie)
            requires root.Valid()
            ensures forall x :: x in root.repr ==> x.Valid()
            decreases root.repr
        {
            if root.children.Values == {} {

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
                        assert node in Union(set x | x in root.children.Values :: x.repr);
                        UnionContains(set x | x in root.children.Values :: x.repr, node);
                        var x :| x in root.children.Values && node in x.repr;
                        ValidImpliesAllValid(x); 
                        assert node.Valid();
                    }
                }
            }
        }
        lemma AllChildrenInRepr(root: Trie, child: Trie)
            requires root.Valid()
            requires child in root.repr
            ensures child.repr <= root.repr
            decreases root.repr
        {
            if root.children.Values == {} {
                assert child == root;
                assert child.children.Values < root.repr;
            } else {
                if child == root {}
                else if child in root.children.Values {
                    assert child in root.children.Values;
                    assert child.children.Values < root.repr;
                } else {
                    assert child in Union(set x | x in root.children.Values :: x.repr);
                    UnionContains(set x | x in root.children.Values :: x.repr, child);
                    // var x :| x in root.children.Values && child in x.repr;
                }
            }
        }

        twostate lemma CurrentChildrenNotInSpineSet(root: Trie, current: Trie, spine: seq<Trie>, spineSet: set<Trie>, reprSpine: set<Trie>, added: set<Trie>)
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

        twostate lemma  UpdatedCurrentValid(current: Trie, child: Trie, updates: map<char, Trie>, c: char)
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
            requires spine[0] == this
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
                                assert spine[|spine| - 1].repr <= spine[i].ChildUnion();
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

        method {:verify } {:vcs_split_on_every_assert} insert(word: string)
            requires this.Valid()
            ensures this.Valid()
            modifies this, repr, children.Values, ChildUnion()
        {
            var current := this;
            ghost var allTries := this.repr;
            ghost var spine: seq<Trie> := [this];
            ghost var spineSet: set<Trie> := {this};
            ghost var reprSpine: set<Trie> := {this};
            assert this.ChildUnion() < this.repr;
            ValidImpliesAllValid(this);
            assert children.Values < allTries;
            ghost var added: set<Trie> := {};
            assert forall x :: x in repr ==> allocated(x);
            for i := 0 to |word| 
                invariant forall x :: x in repr ==> x in old(repr) || x in added
                invariant repr == old(repr) + added
                // invariant forall x :: x in repr ==> allocated(x)
                invariant forall y :: y in added ==> fresh(y)
                invariant forall x :: x in added ==> x.repr < allTries
                invariant forall x :: x in allTries ==> x in old(repr) + added
                invariant forall x :: x in reprSpine ==> x in old(repr)
                invariant spineSet == reprSpine + added
                invariant reprSpine !! added
                invariant |spine| > 0
                invariant forall x :: x in spine ==> x in allTries
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
                invariant current.children.Values < allTries
                invariant current.children.Values !! spineSet
                invariant repr <= allTries
                invariant this in allTries
                invariant current in allTries
                invariant current.Valid()
                invariant this.Valid()
                invariant forall node :: node in allTries ==> node.Valid()
                // modifies allTries
                modifies repr
                modifies current
                modifies current.children.Values
            {
                if word[i] in current.children {
                    assert current in allTries;
                    assert word[i] in current.children.Keys;
                    var childTrie := current.children[word[i]];
                    if childTrie in repr {
                    assert childTrie in current.children.Values;
                    AllChildrenInRepr(this, childTrie);
                    assert current.children[word[i]].repr  <= allTries;
                    } else {
                        assert childTrie in added;
                        assert childTrie !in repr;
                        assert childTrie in current.children.Values;
                        assert current.children[word[i]].repr  < allTries;
                    }
                    current := current.children[word[i]];
                    spine := spine + [current];
                    spineSet := spineSet + {current};
                    if current !in added {
                        reprSpine := reprSpine + {current};
                    }
                    SpineRepr(this, spine);
                    assert current.children.Values < allTries;
                    assert forall x :: x in allTries ==> x.Valid();
                    // CurrentChildrenNotInSpineSet(this, current, spine, spineSet, reprSpine, added);
                } else {
                    ghost var oldAllTries := allTries;
                    var child := new Trie();
                    assert fresh(child);
                    assert child !in allTries; 
                    assert forall x :: x in allTries ==> x.Valid();
                    added := added + {child};
                    allTries := allTries + {child};
                    label BeforeUpdate:
                    // assert current in repr || current in added;
                    // if current !in repr {
                    //     assert current in added;
                    //     assert current.children.Values < allTries;
                    // }else{
                    //     assert current in repr;
                    //     assert current.children.Values < allTries;
                    // }
                    assert child.Valid();
                    ghost var oldc := current.children;
                    var updatedChildren := current.children[word[i] := child];
                    assert updatedChildren[word[i]] == child;
                    assert child in updatedChildren.Values;
                    current.children := updatedChildren;
                    // for k := 0 to |spine| 
                    //     invariant forall x :: x in spine[0..k] ==> child in x.repr
                    // {
                    //     if spine[k] in repr {
                    //         assert spine[k] in allTries;
                    //         AllChildrenInRepr(this, spine[k]);
                    //         assert spine[k].repr <= allTries;
                    //         // assert spine[i].Valid();
                    //     } else {
                    //         assert spine[k] in added;
                    //         assert spine[k].repr <= allTries;
                    //         // assert spine[i].Valid();
                    //     }
                    //    spine[k].repr := spine[k].repr + {child};
                    // }
                    if oldc.Values == {} {
                        assert current.children.Values == {child};
                    } else {
                        assert child !in oldc.Values;
                        assert forall k :: k in oldc.Keys ==> k in current.children.Keys && current.children[k] == oldc[k];
                        assert forall x :: x in oldc.Values ==> x in current.children.Values;
                        assert current.children.Values == oldc.Values+{child};
                    }
                    assert current.children.Values < allTries;
                    current.repr := current.repr + {child};
                    UpdatedCurrentValid@BeforeUpdate(current, child, updatedChildren, word[i]);
                    assert current.repr == old@BeforeUpdate(current.repr) + {child};
                    assert child in current.repr;
                    assert current.Valid();
                    label AfterUpdate:
                    var k := |spine| - 1;
                    ghost var rechanged: set<Trie> := {};
                    while k >= 0
                        invariant -1 <= k < |spine|
                        invariant spine[|spine|-1] == current
                        invariant unchanged@AfterUpdate(current) 
                        // invariant current.repr !! 
                        invariant rechanged < spineSet
                        invariant forall node :: node in old@AfterUpdate(repr)- spineSet ==> unchanged@AfterUpdate(node)
                        invariant forall x :: x in spine[(k+1)..] ==> child in x.repr
                        invariant forall x :: x in spine[(k+1)..] ==> x.Valid()
                        invariant forall x :: x in (repr - spineSet) ==> (x in old@AfterUpdate(this.repr) && unchanged@AfterUpdate(x))
                    {
                        if k == |spine| -1 {
                            assert spine[k] == current;
                            assert child in spine[k].repr;
                            assert spine[k].Valid();
                        } else {
                            rechanged := rechanged + {spine[k]};
                            spine[k].repr := spine[k].repr + {child};
                            assert spine[k].Valid();
                        }
                        // if spine[k] in repr {
                        //     assert spine[k] in allTries;
                        //     AllChildrenInRepr(this, spine[k]);
                        //     assert spine[k].repr <= allTries;
                        //     // assert spine[i].Valid();
                        // } else {
                        //     assert spine[k] in added;
                        //     assert spine[k].repr <= allTries;
                        //     // assert spine[i].Valid();
                        // }
                       k := k - 1;
                    }
                    assert spine[0] == this;
                    assert spine[0].Valid();
                    ValidImpliesAllValid(this);
                    current := child;
                    spine := spine + [current];
                    spineSet := spineSet + {current};
                    if current in old(repr) {
                        reprSpine := reprSpine + {current};
                    }
                    SpineRepr(this, spine);
                    // CurrentChildrenNotInSpineSet(this, current, spine, spineSet, reprSpine, added);
                }
            }
            assert current in allTries;
            current.isWord := true;
        }
    }
}