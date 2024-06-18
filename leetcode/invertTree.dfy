include "../lib/seq.dfy"
module InvertBinaryTree {
    /**
    * https://leetcode.com/problems/invert-binary-tree/description/
    * Definition for a binary tree node.
    class TreeNode {
        val: number
        left: TreeNode | null
        right: TreeNode | null
        constructor(val?: number, left?: TreeNode | null, right?: TreeNode | null) {
            this.val = (val===undefined ? 0 : val)
            this.left = (left===undefined ? null : left)
            this.right = (right===undefined ? null : right)
        }
    }

    function invertTree(root: TreeNode | null): TreeNode | null {
        if(root == null) return null;
        let leftChild = invertTree(root.left);
        let rightChild = invertTree(root.right);
        root.right = leftChild;
        root.left = rightChild;
        return root;
    };
    */
    import opened SeqCustom
    class TreeNode {
        var val: int
        var left: TreeNode?
        var right: TreeNode?
        var repr: set<TreeNode>
        var parent: TreeNode?
        var parentRepr: set<TreeNode>

        constructor(val: int, left: TreeNode?, right: TreeNode?)
            requires left != null ==> left.Valid()
            requires right != null ==> right.Valid()
            requires left != null && right != null ==> left.repr !! right.repr
            ensures this.val == val
            ensures this.left == left
            ensures this.right == right
            ensures left != null ==> this !in left.repr
            ensures right != null ==> this !in right.repr
            ensures Valid()
            ensures ParentValid()
            ensures parentRepr == {}
        {
            this.val := val;
            this.left := left;
            this.right := right;
            var leftRepr := if left != null then {left}+left.repr else {};
            var rightRepr := if right != null then {right}+right.repr else {};
            this.repr := {this} + leftRepr + rightRepr;
            this.parent := null;
            this.parentRepr := {};
            reveal ParentValid();
        }

        ghost predicate Valid()
            reads this, repr
            decreases repr
        {
            this in repr &&
            (this.left != null ==>
            (this.left in repr
            && this !in this.left.repr
            && this.left.repr < repr
            && this.left.Valid()
            ))
            && (this.right != null ==>
            (this.right in repr
            && this !in this.right.repr
            && this.right.repr < repr
            && this.right.Valid())) &&
            (this.left != null && this.right != null ==> this.left.repr !! this.right.repr && this.repr == {this} + this.left.repr + this.right.repr)
            && (this.left != null && this.right == null ==> this.repr == {this} + this.left.repr)
            && (this.right != null && this.left == null ==> this.repr == {this} + this.right.repr)
            && (this.right == null && this.left == null ==> this.repr == {this})
        }

        opaque ghost predicate ParentValid() 
            reads this, parentRepr
            decreases parentRepr
        {
            (this !in this.parentRepr) &&
            ((this.parent == null ==> this.parentRepr == {}) ||
            (
                (this.parent != null && 
                this.parent in this.parentRepr &&
                this != parent && 
                this.parentRepr == {this.parent}+this.parent.parentRepr && 
                this.parent !in this.parent.parentRepr
                ) && (this.parent.left == this || this.parent.right == this) && 
            this.parent.ParentValid()))

        }

        method setParent(parent: TreeNode)
            requires parent.ParentValid()
            requires parent.Valid()
            requires this == parent.left || this == parent.right
            requires this != parent
            requires this !in parent.parentRepr
            requires parent.left != null ==> allocated(parent.left)
            requires parent.right != null ==> allocated(parent.right)
            requires this.Valid()
            modifies this, parent
            ensures parent.ParentValid()
            ensures this.ParentValid()
            // ensures parent.left != null ==> unchanged(parent.left)
            // ensures parent.right != null ==> unchanged(parent.right)
            ensures old(parent.left) == parent.left
            ensures old(parent.right) == parent.right
            ensures old(parent.parentRepr) == parent.parentRepr
            ensures old(repr) == repr
            ensures parent.Valid()
            ensures this.Valid()
        {
            this.parent := parent;
            this.parentRepr := {parent}+parent.parentRepr;
            reveal ParentValid();
        }

        ghost predicate iterativeValid()
            reads this, repr
            decreases repr
            requires this.Valid()
        {
            forall x :: x in PreorderTraversal(this) ==> x in repr
        }

        method  invertBinaryTree() returns (newRoot: TreeNode?)
            modifies this.repr
            requires this.Valid()
            ensures newRoot == this && newRoot.right == old(this.left) && newRoot.left == old(this.right)
            ensures newRoot.repr == old(this.repr) && newRoot.Valid()
            ensures forall node :: node in this.repr ==> node.right == old(node.left) && node.left == old(node.right)
            ensures newRoot.Valid()
            decreases repr
        {
            var leftChild: TreeNode? := null;
            if left != null {
                leftChild := left.invertBinaryTree();
            }
            var rightChild: TreeNode? := null;
            if right != null {
                rightChild := right.invertBinaryTree();
            }
            right := leftChild;
            left := rightChild;
            return this;
        }
        
    function TreeSize(): nat 
        reads this, repr
        requires this.Valid()
        ensures |repr| == TreeSize()
        decreases repr
    {
        if this.left != null && this.right != null then
            1 + this.left.TreeSize() + this.right.TreeSize()
        else if this.left != null && this.right == null then
            1 + this.left.TreeSize()
        else if this.left == null && this.right != null then
            1 + this.right.TreeSize()
        else
            1
    }

      
    }

    function PreorderTraversal(root: TreeNode): seq<TreeNode>
        reads root.repr
        requires root.Valid()
        // ensures forall x :: x in PreorderTraversal(root) ==> x.Valid()
        ensures forall x :: x in root.repr ==> x in PreorderTraversal(root)
        ensures forall x :: x in PreorderTraversal(root) ==> x in root.repr
        ensures forall k :: 0 <= k < |PreorderTraversal(root)| ==> PreorderTraversal(root)[k] in root.repr && PreorderTraversal(root)[k].Valid()
        ensures forall x :: x in PreorderTraversal(root) ==> x.Valid()
        ensures distinct(PreorderTraversal(root))
        ensures forall k :: 0 <= k < |PreorderTraversal(root)| ==> PreorderTraversal(root)[k] in root.repr
        ensures ToSet(PreorderTraversal(root)) == root.repr
        ensures root in PreorderTraversal(root) 
        ensures root.left != null ==> root.left in PreorderTraversal(root)
        ensures root.right != null ==> root.right in PreorderTraversal(root)
        // ensures forall k :: 0 <= k < |PreorderTraversal(root)| ==> forall child :: child in PreorderTraversal(root)[k].repr && child != child in PreorderTraversal(root)[k] ==> exists j :: k < j < |PreorderTraversal(root)| && PreorderTraversal(root)[j] == child
    {
    if root.left != null && root.right != null then [root]+PreorderTraversal(root.left)+PreorderTraversal(root.right) else if root.left != null then [root]+PreorderTraversal(root.left) else if root.right != null then [root]+PreorderTraversal(root.right) else [root]
    }

    lemma traversalSize(root: TreeNode)
        requires root.Valid()
        ensures |PreorderTraversal(root)| == root.TreeSize()
        ensures |PreorderTraversal(root)| == |root.repr|
        decreases root.repr
    {
        assert root.Valid(); 
        if root.left != null && root.right != null {
            traversalSize(root.left);
            traversalSize(root.right);
            assert |PreorderTraversal(root)| == 1 + root.left.TreeSize() + root.right.TreeSize();
        }else if root.left != null && root.right == null {
            traversalSize(root.left);
            assert |PreorderTraversal(root)| == 1 + root.left.TreeSize();
        }else if root.left == null && root.right != null {
            traversalSize(root.right);
            assert |PreorderTraversal(root)| == 1 + root.right.TreeSize();
        }else {
            assert |PreorderTraversal(root)| == 1;
        }
    }

    lemma subsetsSmaller<T>(a: set<T>, b: set<T>)
        requires a < b
        ensures |a| < |b|
    {
        if something :| something in a {
            if a-{something} == {} {
                var x :| x in b && x != something;
                subsetsSmaller(a-{something}, b);
                assert b == {something, x}+(b-{something, x});
                assert |b| >= 2;
                // assert |b| == 
            }else{
                var x :| x in b && x != something && x !in a;
                assert b == {something, x}+(b-{something, x});
                assert |b| >= 2;

                subsetsSmaller(a-{something}, b-{something});
            }
        }else{
            assert a == {};
            assert |a| == 0;
        }
    } 

    lemma childTraversalSize(root: TreeNode, node: TreeNode)
        requires root.Valid()
        requires node.Valid()
        requires node != root
        requires node in root.repr
        ensures |PreorderTraversal(node)| < |PreorderTraversal(root)|
    {
        traversalSize(root);
        traversalSize(node);
        ChildNodesReprAreLess(root, node);
        assert |PreorderTraversal(node)| == |node.repr|;
        assert |PreorderTraversal(root)| == |root.repr|;
        subsetsSmaller(node.repr, root.repr);
        assert |PreorderTraversal(node)| < |PreorderTraversal(root)|;
    }

    lemma PreorderTraversalSlices(root: TreeNode)
      requires root.Valid()
      // ensures root.left != null && root.right != null ==> PreorderTraversal(root)[]
      ensures PreorderTraversal(root)[..1] == [root]
      ensures root.left != null ==> PreorderTraversal(root)[1..|PreorderTraversal(root.left)|+1] == PreorderTraversal(root.left)
      ensures root.right != null && root.left == null ==> PreorderTraversal(root)[1..|PreorderTraversal(root.right)|+1] == PreorderTraversal(root.right)
      ensures root.right != null && root.left != null ==> PreorderTraversal(root)[|PreorderTraversal(root.left)|+1..] == PreorderTraversal(root.right)
    {}

    //Still doesn't verify, definitely seems like it should. Is it a trigger problem?
    lemma {:verify false} {:vcs_split_on_every_assert} PreorderTraversalSubSlices(root: TreeNode)
        requires root.Valid()
        ensures forall node :: node in root.repr ==> exists k,j :: 0<=k<=j<= |PreorderTraversal(root)| && PreorderTraversal(node) == PreorderTraversal(root)[k..j]
        decreases root.repr
    {
        forall node | node in root.repr 
            ensures exists k,j :: 0<=k<=j<= |PreorderTraversal(root)| && PreorderTraversal(node) == PreorderTraversal(root)[k..j]
        {
            if node == root {
                assert PreorderTraversal(node) == PreorderTraversal(root)[0..|PreorderTraversal(root)|];
                // assert exists k,j :: 0<=k<=j<= |PreorderTraversal(root)| && PreorderTraversal(node) == PreorderTraversal(root)[k..j];
            }else if node == root.left {
                if root.right == null {
                    assert PreorderTraversal(root) == [root]+PreorderTraversal(root.left);
                    assert PreorderTraversal(node) == PreorderTraversal(root)[1..|PreorderTraversal(root)|];
                }else{
                    assert PreorderTraversal(root) == [root]+PreorderTraversal(root.left)+PreorderTraversal(root.right);
                    assert |PreorderTraversal(root.left)| < |PreorderTraversal(root)|;
                    assert PreorderTraversal(node) == PreorderTraversal(root)[1..|PreorderTraversal(node)|+1];
                    childTraversalSize(root, node);
                    assert 0 <= 1 <= |PreorderTraversal(node)|+1 <= |PreorderTraversal(root)|;
                }
                // assert exists k,j :: 0<=k<=j<= |PreorderTraversal(root)| && PreorderTraversal(node) == PreorderTraversal(root)[k..j];
            }else if node == root.right {
                if root.left == null {
                    assert PreorderTraversal(root) == [root]+PreorderTraversal(root.right);
                    assert PreorderTraversal(node) == PreorderTraversal(root)[1..|PreorderTraversal(root)|];
                }else{
                    assert PreorderTraversal(root) == [root]+PreorderTraversal(root.left)+PreorderTraversal(root.right);
                    childTraversalSize(root, node);
                    childTraversalSize(root, root.left);
                    // assert |PreorderTraversal(root.left)| < |PreorderTraversal(root)|;
                    // assert |PreorderTraversal(root.right)| < |PreorderTraversal(root)|;
                    assert PreorderTraversal(node) == PreorderTraversal(root)[(1+|PreorderTraversal(root.left)|)..|PreorderTraversal(root)|];
                    assert 0 <= 1+|PreorderTraversal(root.left)| <= |PreorderTraversal(root)|;
                }
                // assert exists k,j :: 0<=k<=j<= |PreorderTraversal(root)| && PreorderTraversal(node) == PreorderTraversal(root)[k..j];
            }else if node != root && node != root.right && node != root.left {
                childInRootRepr(root, node);
                if root.right == null && root.left == null {
                    assert false;
                } else if root.right != null && root.left == null {
                    assert node in root.right.repr;
                    PreorderTraversalSubSlices(root);
                    PreorderTraversalSlices(root.right);
                    childTraversalSize(root, root.right);
                    childTraversalSize(root, node);
                    childTraversalSize(root.right, node);
                    assert node in PreorderTraversal(root.right);
                    var x,y :| 0 <= x <= y < |PreorderTraversal(root.right)| && PreorderTraversal(node) == PreorderTraversal(root.right)[x..y];
                    assert PreorderTraversal(root)[1..|PreorderTraversal(root.right)|+1] == PreorderTraversal(root.right);
                    assert PreorderTraversal(root)[1+x..1+y] == PreorderTraversal(node);
                    assert 0 <= 1+x <= 1+y <= |PreorderTraversal(root)|;
                } else if root.right == null && root.left != null {
                    assert node in root.left.repr;
                    PreorderTraversalSubSlices(root);
                    PreorderTraversalSlices(root.left);

                    childTraversalSize(root, root.left);
                    childTraversalSize(root, node);
                    childTraversalSize(root.left, node);
                    assert node in PreorderTraversal(root.left);
                    var x,y :| 0 <= x <= y < |PreorderTraversal(root.left)| && PreorderTraversal(node) == PreorderTraversal(root.left)[x..y];
                    assert PreorderTraversal(root)[1..|PreorderTraversal(root.left)|+1] == PreorderTraversal(root.left);
                    assert PreorderTraversal(root)[1+x..1+y] == PreorderTraversal(node);
                    assert 0 <= 1+x <= 1+y <= |PreorderTraversal(root)|;
                }else if root.right != null && root.right != null {
                    if node in root.right.repr {
                    PreorderTraversalSlices(root);
                    PreorderTraversalSubSlices(root.right);
                    childTraversalSize(root, root.right);
                    childTraversalSize(root, node);
                    childTraversalSize(root.right, node);
                    assert node in PreorderTraversal(root.right);

                    var x,y :| 0 <= x <= y < |PreorderTraversal(root.right)| && PreorderTraversal(node) == PreorderTraversal(root.right)[x..y];
                    assert PreorderTraversal(root)[|PreorderTraversal(root.left)|+1..] == PreorderTraversal(root.right);
                    assert PreorderTraversal(root)[|PreorderTraversal(root.left)|+x..|PreorderTraversal(root.left)|+y] == PreorderTraversal(node);
                    assert 0 <= |PreorderTraversal(root.left)|+x <= |PreorderTraversal(root.left)|+y <= |PreorderTraversal(root)|;
                    }else if node in root.left.repr {
                    PreorderTraversalSlices(root);
                    PreorderTraversalSubSlices(root.left);
                    childTraversalSize(root, root.left);
                    childTraversalSize(root, node);
                    childTraversalSize(root.left, node);
                    assert node in PreorderTraversal(root.left);
                    var x,y :| 0 <= x <= y < |PreorderTraversal(root.left)| && PreorderTraversal(node) == PreorderTraversal(root.left)[x..y];
                    assert PreorderTraversal(root)[1..|PreorderTraversal(root.left)|+1] == PreorderTraversal(root.left);
                    assert PreorderTraversal(root)[1+x..1+y] == PreorderTraversal(node);
                    assert 0 <= 1+x <= 1+y <= |PreorderTraversal(root)|;

                    }
                }
                assert exists k,j :: 0<=k<=j <= |PreorderTraversal(root)| && PreorderTraversal(node) == PreorderTraversal(root)[k..j];
            }else{
                assert false;
            }
            // assert node != root && node != root.right && node != root.left;
                assert exists k,j :: 0<=k<=j<= |PreorderTraversal(root)| && PreorderTraversal(node) == PreorderTraversal(root)[k..j];
        }
        // assert forall node :: node in root.repr ==> exists k,j :: 0<=k<=j<= |PreorderTraversal(root)| && PreorderTraversal(node) == PreorderTraversal(root)[k..j];
    }

    lemma PreorderTraversalEqualToRepr(root: TreeNode)
        requires root.Valid()
        ensures ToSet(PreorderTraversal(root)) == root.repr
    {
        // var xs := ToSet(PreorderTraversal(root));
        // forall x | x in xs
        // ensures x in root.repr
        // {
        //     assert x in xs;
        //     assert x in PreorderTraversal(root);
        //     assert x in root.repr;
        // }
        // assert ToSet(PreorderTraversal(root)) <= root.repr;

    }

    lemma PreorderTraversalIndexAll(root: TreeNode)
        requires root.Valid()
        ensures forall x :: x in root.repr ==> exists k :: 0 <= k < |PreorderTraversal(root)| && PreorderTraversal(root)[k] == x
    {
        PreorderTraversalEqualToRepr(root);
        forall x | x in root.repr 
            ensures exists k :: 0 <= k < |PreorderTraversal(root)| && PreorderTraversal(root)[k] == x
        {
            
        }
    }

    lemma {:verify false} PreorderTraversalSubstrings(root: TreeNode)
        requires root.Valid()
        ensures root.left != null ==> isSubstring(PreorderTraversal(root.left), PreorderTraversal(root))
        ensures root.right != null ==> isSubstring(PreorderTraversal(root.right), PreorderTraversal(root))
    {

    if root.left != null && root.right != null {
        calc {
            PreorderTraversal(root);
            [root]+PreorderTraversal(root.left)+PreorderTraversal(root.right);
        }
        var k := 1;
        var j := |PreorderTraversal(root.left)|+1;
        assert 0 <= k <= j <= |PreorderTraversal(root)| && PreorderTraversal(root.left) == PreorderTraversal(root)[1..|PreorderTraversal(root.left)|+1];

        var s := 1+|PreorderTraversal(root.left)|;
        var t := |PreorderTraversal(root)|;
        assert 0 <= s <= t <= |PreorderTraversal(root)| && PreorderTraversal(root.right) == PreorderTraversal(root)[s..t];
    }else if root.left != null && root.right == null {
        calc {
            PreorderTraversal(root);
            [root]+PreorderTraversal(root.left);
        }
        var k := 1;
        var j := |PreorderTraversal(root.left)|+1;
        assert 0 <= k <= j <= |PreorderTraversal(root)| && PreorderTraversal(root.left) == PreorderTraversal(root)[1..j];
    }else if root.left == null && root.right != null {
        calc {
            PreorderTraversal(root);
            [root]+PreorderTraversal(root.right);
        }
        var k := 1;
        var j := |PreorderTraversal(root.right)|+1;
        assert 0 <= k <= j <= |PreorderTraversal(root)| && PreorderTraversal(root.right) == PreorderTraversal(root)[1..j];
    }
    }

    // lemma AllChildrenTraversalsAreSubstrings(root: TreeNode) 
    //     requires root.Valid()
    //     ensures forall x :: x in root.repr && x in PreorderTraversal(root) ==> isSubstring(PreorderTraversal(x), PreorderTraversal(root))
    // {
    //     forall x | x in root.repr && x in PreorderTraversal(root) 
    //         ensures isSubstring(PreorderTraversal(x), PreorderTraversal(root))
    //     {
    //         if x == root {

    //         }else if x == root.left || x == root.right {
    //            PreorderTraversalSubstrings(root); 
    //         }else {
    //             if root.left != null && x in root.left.repr {
    //                 AllChildrenTraversalsAreSubstrings(root.left);
    //             }
    //             if root.right != null && x in root.right.repr {
    //                 AllChildrenTraversalsAreSubstrings(root.right);
    //             }
    //         }
    //     }
    // }

    predicate seqElement<A(==)>(s: seq<A>, elem: A, k: nat)

    {
        0 <= k < |s| && elem in s && s[k] == elem
    }

    lemma {:verify } PreorderTraversalChildrenAreLater1(root: TreeNode)
        requires root.Valid()
        //would not verify until asserted that x was also in PreorderTraversal(root)
        ensures forall x :: x in root.repr && x in PreorderTraversal(root) ==> exists k: nat :: 0 <= k < |PreorderTraversal(root)| && PreorderTraversal(root)[k] == x
    {
        forall x | x in root.repr 
            ensures exists k: nat :: 0 <= k < |PreorderTraversal(root)| && PreorderTraversal(root)[k] == x
        {
            assert x in PreorderTraversal(root);
            seqbusiness(PreorderTraversal(root), x);
        }
    }


    lemma {:verify true} PreorderTraversalChildrenAreLater(root: TreeNode)
        requires root.Valid()
        //the following does not verify
        ensures forall x :: x in root.repr && x in PreorderTraversal(root) && x != root ==> exists k: nat :: 0 < k < |PreorderTraversal(root)| && PreorderTraversal(root)[k] == x
    {
        
        // forall x | x in root.repr && x in PreorderTraversal(root) && x != root
            // ensures exists k: nat :: 0 < k < |PreorderTraversal(root)| && PreorderTraversal(root)[k] == x
        // {
            // PreorderTraversalChildrenAreLater1(root);
            // var k :| 0 <= k < |PreorderTraversal(root)| && PreorderTraversal(root)[k] == x;
            // assert PreorderTraversal(root)[0] == root;
        // }
        // but it verifies here, at least I get the green checkmark
        // assert forall x :: x in root.repr ==> exists k: nat :: 0 <= k < |PreorderTraversal(root)| && PreorderTraversal(root)[k] == x;
    }

    lemma {:verify true} childInRootRepr(root: TreeNode, child: TreeNode)
        requires root.Valid()
        requires child != root && child in root.repr
        // requires k < |PreorderTraversal(root)| && PreorderTraversal(root)[k] == child
        // ensures child.left != null ==> child.left in PreorderTraversal(root)
        // ensures child.right != null ==> child.right in PreorderTraversal(root)
        // ensures child.left != null ==> child.left in root.repr
        // ensures child.right != null ==> child.right in root.repr
        ensures root.left != null && root.right != null ==> child in root.left.repr || child in root.right.repr
        ensures root.left != null && root.right == null ==> child in root.left.repr
        ensures root.left == null && root.right != null ==> child in root.right.repr
    {
        // assert child.Valid();
        // assert child.left != null ==> child.left in PreorderTraversal(root);
        if child.left != null {
            // assert child.left in child.repr;
            // assert child.left in root.repr;
        }
        if root.left != null && root.right != null {
            assert child in root.left.repr || child in root.right.repr;
        }else if root.left == null && root.right == null {
            assert child in root.right.repr;
        }else if root.right == null && root.left != null {
            assert child in root.left.repr;
        }else if root.right == null && root.left == null {
            // assert root.right == null;
            // assert root.left == null;
            assert root.repr == {root};
            assert false;
        }
    }

    lemma {:verify true} childChildrenInRootRepr(root: TreeNode, child: TreeNode)
        requires root.Valid()
        requires child != root && child in root.repr
        ensures child.repr < root.repr
        decreases root.repr
    {
        childInRootRepr(root, child);
        if root.left != null && child in root.left.repr {
            if child == root.left {

            }else{
                childChildrenInRootRepr(root.left, child);
                assert child.repr < root.left.repr;
            }
        }

        if root.right != null && child in root.right.repr {
            if child == root.right {

            }else{

                assert child.repr <= root.right.repr;
            }
        }
    }


    lemma {:verify true} later(root: TreeNode, child: TreeNode, k: nat)
        requires root.Valid()
        requires child != root && child in root.repr
        requires k < |PreorderTraversal(root)| && PreorderTraversal(root)[k] == child
        // ensures child.left != null ==> exists j: nat :: k < j < |PreorderTraversal(root)| && PreorderTraversal(root)[j] == child.left
        // ensures child.right != null ==> exists j: nat :: k < j < |PreorderTraversal(root)| && PreorderTraversal(root)[j] == child.right
    {
        childChildrenInRootRepr(root, child);
        // assert child.Valid();
        // assert child.left != null ==> child.left in PreorderTraversal(root);
        assert child in PreorderTraversal(root);
        if child.left != null {
            assert child.left in child.repr;
            assert child.left in root.repr;
        }
    }


    lemma {:verify false} PreorderTraversalChildrenAreLater3(root: TreeNode, elem: TreeNode, k: nat) 
        requires root.Valid()
        requires elem in root.repr
        requires elem in PreorderTraversal(root)
        requires PreorderTraversal(root)[k] == elem
        // ensures forall child :: child in elem.repr && child in PreorderTraversal(root) && child != elem ==> exists j: nat :: k < j < |PreorderTraversal(root)| && PreorderTraversal(root)[j] == child
    {

    }

    lemma seqbusiness<A>(s: seq<A>, elem: A)
        requires elem in s
        ensures exists k:nat :: 0 <= k < |s| && s[k] == elem
        ensures exists k:nat :: seqElement(s, elem, k) 
    {
        assert elem in s;
        assert exists k:nat :: 0 <= k < |s| && s[k] == elem && seqElement(s, elem, k);
    }

    method swapChildren(root: TreeNode) returns (newRoot: TreeNode)
        modifies root
        requires root.Valid()
        ensures root == newRoot && newRoot.Valid()
        ensures root.right == old(root.left) && root.left == old(root.right)
        ensures forall x :: x in root.repr && x != root ==> unchanged(x)
    {

        var temp := root.left;
        root.left := root.right;
        root.right := temp;
        return root;
    }

    method  invertBinaryTree(root: TreeNode?) returns (newRoot: TreeNode?)
        modifies if root != null then root.repr else {}
        requires root != null ==> root.Valid()
        ensures root == null ==> newRoot == null
        ensures root != null ==> newRoot != null && newRoot.repr == old(root.repr) && newRoot.Valid()
        ensures root != null ==> newRoot == root && newRoot.right == old(root.left) && root.left == old(root.right)
        ensures root != null ==> forall node :: node in newRoot.repr ==> node.right == old(node.left) && node.left == old(node.right)
        decreases if root == null then {} else root.repr
    {
        if root != null {
            var leftChild := invertBinaryTree(root.left);
            var rightChild := invertBinaryTree(root.right);
            root.right := leftChild;
            root.left := rightChild;
            return root;
        }else{
            return null;
        }
    }

    lemma ChildNodesAreInRoot(root: TreeNode, child: TreeNode)
        requires root.Valid()
        requires (root.left != null && child == root.left) || (root.right != null && root.right == child)
        ensures child in root.repr
    {

    }

    lemma ChildChildrenNodesAreInRoot(root: TreeNode, child: TreeNode)
        requires root.Valid()
        requires (root.left != null && (child == root.left.left || child == root.left.right)) || (root.right != null && (root.right.left == child || root.right.right == child))
        ensures child in root.repr
    {

    }

    lemma ChildNodesAreValid(root: TreeNode, child: TreeNode)
        requires root.Valid()
        requires child in root.repr
        decreases root.repr
        ensures child.repr <= root.repr
        ensures child.Valid()
    {
        if child == root {
        }else if child == root.left {

        }else if child == root.right {

        }else if root.left != null && root.right != null {
            assert root.repr == {root} + root.left.repr + root.right.repr;
            if child in root.left.repr {
                ChildNodesAreValid(root.left, child);
            }else if child in root.right.repr {
                ChildNodesAreValid(root.right, child);
            }else{
                assert false;
            }
        }else if root.right != null {

        }else if root.left != null {

        }else{
            assert false;
        }
    }

    lemma ChildNodesReprAreLess(root: TreeNode, child: TreeNode)
        requires root.Valid()
        requires child in root.repr
        requires child != root
        decreases root.repr
        ensures child.repr < root.repr
        ensures child.Valid()
    {
        if child == root.left {

        }else if child == root.right {

        }else if root.left != null && root.right != null {
            assert root.repr == {root} + root.left.repr + root.right.repr;
            if child in root.left.repr {
                ChildNodesReprAreLess(root.left, child);
            }else if child in root.right.repr {
                ChildNodesReprAreLess(root.right, child);
            }else{
                assert false;
            }
        }else if root.right != null {

        }else if root.left != null {

        }else{
            assert false;
        }
    }


    twostate lemma ValidSwappingStillValid(root: TreeNode, child: TreeNode)
        requires root.Valid()
        requires child in root.repr
        requires child.left == old(child.right) && child.right == old(child.left)
        ensures root.Valid()
    {
        ChildNodesAreValid(root,child);
        assert child.Valid();
    }

    twostate lemma ValidSwapping(root: TreeNode)
        requires root.Valid()
        requires root.left == old(root.right) && root.right == old(root.left)
        ensures root.Valid()
    {
        // ChildNodesAreValid(root,child);
        // assert child.Valid();
    }

    ghost function TreeUnion(nodes: seq<TreeNode>): set<TreeNode>
        reads set x | 0 <= x < |nodes| :: nodes[x]
    {
    if |nodes| > 0 then nodes[0].repr + TreeUnion(nodes[1..]) else {}
    }

    lemma TreeUnionLemma(nodes: seq<TreeNode>)
        ensures forall x :: x in TreeUnion(nodes) ==> exists k :: 0 <= k < |nodes| && x in nodes[k].repr
    {

    }
    
    lemma TreeUnionLemma2(nodes: seq<TreeNode>, node: TreeNode, childnode: TreeNode)
        requires node in nodes
        requires childnode in node.repr
        ensures childnode in TreeUnion(nodes)
    {

    }

    lemma TreeUnionConcat(xs: seq<TreeNode>, ys: seq<TreeNode>)
        requires forall x :: x in xs ==> x.Valid()
        requires forall y :: y in xs ==> y.Valid()
        // requires TreeUnion(xs) !! TreeUnion(ys)
        ensures TreeUnion(xs+ys) == TreeUnion(xs)+TreeUnion(ys)
    {
        if xs == [] {
            assert xs+ys == ys;
        }else{
            assert xs == [xs[0]]+xs[1..];
            assert TreeUnion(xs) == xs[0].repr + TreeUnion(xs[1..]);
            TreeUnionConcat(xs[1..], ys);
            assert TreeUnion(xs[1..])+ TreeUnion(ys) == TreeUnion(xs[1..]+ys);
            calc{
                TreeUnion(xs+ys);
                TreeUnion(([xs[0]]+xs[1..])+ys);
                {assert ([xs[0]]+xs[1..])+ys == [xs[0]]+(xs[1..]+ys);}
                TreeUnion([xs[0]]+(xs[1..]+ys));
                xs[0].repr+TreeUnion(xs[1..]+ys);
            }
        }
    }
    //fresh ensures that a variable was initialized by a method or two-state function

    method {:verify false} invertBinaryTreeIterative1(root: TreeNode?) returns (newRoot: TreeNode?)
        modifies if root != null then root.repr else {}
        requires root != null ==> root.Valid()
        ensures root == null ==> newRoot == null
        ensures root != null ==> newRoot == root && newRoot.repr == old(root.repr)
        // ensures root != null ==> newRoot != null && newRoot.repr == old(root.repr) && newRoot.Valid()
        // ensures root != null ==> forall node :: node in newRoot.repr ==> node.right == old(node.left) && node.left == old(node.right)
        // ensures root != null ==> newRoot == root && newRoot.right == old(root.left) && root.left == old(root.right)
    {
        if root == null {
            return null;
        }

        var nodes := PreorderTraversal(root);
        assert forall k :: 0 <= k < |nodes| ==> nodes[k] in root.repr && nodes[k].Valid();
        assert distinct(nodes);
        ghost var visited: set<TreeNode> := {};
        ghost var unvisited: set<TreeNode> := root.repr;
        var i := 0;
        while i < |nodes| 
            modifies root.repr
            invariant 0 <= i <= |nodes|
            invariant root.repr == old(root.repr)
            invariant forall k::i < k < |nodes| ==> unchanged(nodes[k])
            invariant visited !! unvisited
            invariant visited == set k | 0 <= k < i  :: nodes[k]
            invariant forall x :: x in nodes ==> x.Valid()
            invariant forall x :: x in unvisited ==> x.Valid()
            invariant forall x :: x in visited ==> x.Valid()
        //     // invariant root.Valid()
        //     // invariant forall k :: 0<= k < i ==> nodes[k].right == old(nodes[k].left) && nodes[k].left == old(nodes[k].right)
        {
            assert nodes[i] in nodes;
            assert nodes[i] in root.repr;
            assert nodes[i].Valid();
            assert nodes[i].left != null ==> nodes[i].left.Valid();
            assert nodes[i].right != null ==> nodes[i].right.Valid();
            // if nodes[i].left != null {
            //     assert nodes[i].left in unvisited;
            // }

            // if nodes[i].right != null {
            //     assert nodes[i].right in unvisited;
            // }
        // //     var temp := nodes[i].left;
        // //     nodes[i].left := nodes[i].right;
        // //     nodes[i].right := temp;
            // nodes[i].left, nodes[i].right := nodes[i].right, nodes[i].left;
            // assert nodes[i].right == old(nodes[i].left) && nodes[i].left == old(nodes[i].right);
            // ValidSwapping(nodes[i]);
            assert nodes[i].Valid();
        // //     // var newNode := swapChildren(nodes[i]);
        // //     ValidSwappingStillValid(root, nodes[i]);
            visited := visited + {nodes[i]};
            unvisited := unvisited - {nodes[i]};
            i := i + 1;
        }
        return root;
    }

}