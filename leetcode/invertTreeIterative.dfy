include "./invertTree.dfy"

module InvertTreeIterative {
    import opened InvertBinaryTree 

    ghost predicate AllDisjoint(ts: seq<TreeNode>)
        reads set x | 0 <= x < |ts| :: ts[x]
    {
        forall x, y :: 0 <= x < y < |ts| && x != y ==> ts[x].repr !! ts[y].repr
    }

    lemma  AllDisjointMaint(stack: seq<TreeNode>, current: TreeNode)
        requires |stack| > 0
        requires AllDisjoint(stack)
        requires forall x :: x in stack ==> x.Valid()
        requires current == stack[|stack|-1]
        ensures current.left != null && current.right != null ==> AllDisjoint(stack[..|stack|-1]+[current.right, current.left])
        ensures current.left != null && current.right == null ==> AllDisjoint(stack[..|stack|-1]+[current.left])
        ensures current.left == null && current.right != null ==> AllDisjoint(stack[..|stack|-1]+[current.right])
        ensures current.left == null && current.right == null ==> AllDisjoint(stack[..|stack|-1])
    {
            if current.right != null && current.left != null {
                assert current.Valid();
                assert AllDisjoint(stack[..|stack|-1]+[current.right, current.left]);
            } else if current.right != null && current.left == null {
                assert current.Valid();
                assert current.right.repr < current.repr;
                assert AllDisjoint(stack[..|stack|-1]+[current.right]);
            } else if current.right == null && current.left != null {
                assert current.Valid();
                assert AllDisjoint(stack[..|stack|-1]+[current.left]);
            }else {
                assert AllDisjoint(stack[..|stack|-1]);
            }
    }

    lemma  TreeUnionMaint(stack: seq<TreeNode>, current: TreeNode, unvisited: set<TreeNode>)
        requires |stack| > 0
        requires unvisited == TreeUnion(stack)
        requires AllDisjoint(stack)
        requires forall x :: x in stack ==> x.Valid()
        requires current == stack[|stack|-1]
        ensures current.left != null && current.right != null ==> TreeUnion(stack[..|stack|-1]+[current.right, current.left]) == unvisited-{current}
        ensures current.left != null && current.right == null ==> TreeUnion(stack[..|stack|-1]+[current.left]) == unvisited-{current}
        ensures current.left == null && current.right != null ==> TreeUnion(stack[..|stack|-1]+[current.right]) == unvisited-{current}
        ensures current.left == null && current.right == null ==> TreeUnion(stack[..|stack|-1]) == unvisited-{current}
    {
        assert current.Valid();
        assert stack == stack[..|stack|-1]+[stack[|stack|-1]];
        TreeUnionConcat(stack[..|stack|-1],[stack[|stack|-1]]);
        assert TreeUnion(stack) == TreeUnion(stack[..|stack|-1])+TreeUnion([stack[|stack|-1]]);
        assert TreeUnion([stack[|stack|-1]]) == current.repr;
        assert TreeUnion(stack[..|stack|-1]) !! current.repr by {
            forall x | x in TreeUnion(stack[..|stack|-1])
                ensures x !in current.repr
            {
                // var xx :| xx in stack[..|stack|-1] && x in xx.repr;
                TreeUnionLemma(stack[..|stack|-1]);
                var k :| 0 <= k < |stack[..|stack|-1]| && x in stack[..|stack|-1][k].repr;
                assert stack[..|stack|-1][k].repr !! current.repr;
            }
        }
        assert TreeUnion(stack[..|stack|-1]) == unvisited-current.repr;
        if current.left != null && current.right != null {
            assert current.right.repr + current.left.repr + {current} == current.repr;
            assert current.right.repr + current.left.repr == current.repr - {current};
            TreeUnionConcat([current.right],[current.left]);
            assert TreeUnion([current.right, current.left]) == current.right.repr + current.left.repr;
            TreeUnionConcat(stack[..|stack|-1], [current.right, current.left]);
        } else if current.left != null && current.right == null {
            assert current.left.repr == current.repr - {current};
            TreeUnionConcat(stack[..|stack|-1], [current.left]);
            
        }else if current.left == null && current.right != null {
            assert current.right.repr == current.repr - {current};
            TreeUnionConcat(stack[..|stack|-1], [current.right]);

        }else if current.left == null && current.right == null {

        }
    }

    method {:verify } {:vcs_split_on_every_assert} invertBinaryTreeIterative(root: TreeNode?) returns (newRoot: TreeNode?)
        modifies if root != null then root.repr else {}
        requires root != null ==> root.Valid()
        ensures root == null ==> newRoot == null
        // ensures root != null ==> newRoot != null && newRoot.repr == old(root.repr) && newRoot.Valid()
        // ensures root != null ==> newRoot == root && newRoot.right == old(root.left) && root.left == old(root.right)
        // ensures root != null ==> newRoot.repr == old(root.repr)
        ensures root != null ==> newRoot == root
        ensures root != null ==> forall node :: node in newRoot.repr ==> allocated(node)
        // ensures root != null ==> forall node :: node in newRoot.repr ==> node.right == old(node.left) && node.left == old(node.right)
    {
        if root == null {
            return null;
        }
        assert root != null;
        assert root.Valid();
        var nodes := PreorderTraversal(root);
        var stack: seq<TreeNode> := [root];
        assert AllDisjoint(stack);
        ghost var visited: set<TreeNode> := {};
        ghost var unvisited: set<TreeNode> := root.repr;
        assert TreeUnion(stack) == unvisited;
        assert TreeUnion(stack) == root.repr - visited;
        assert root in root.repr;
        assert root.repr <= root.repr;
        assert root in stack;
        traversalSize(root);
        assert |nodes| == |unvisited|;
        var i := 0;
        while |stack| > 0 
            modifies root.repr
            invariant root.Valid()
            invariant root.repr == old(root.repr)
            invariant visited !! unvisited
            invariant visited + unvisited == root.repr
            invariant forall x :: x in stack ==> x in root.repr
            invariant forall x :: x in stack ==> x.Valid()
            invariant AllDisjoint(stack)
            invariant unvisited == TreeUnion(stack)
            invariant forall x :: x in stack ==> x in unvisited
            invariant i == |visited|
            invariant 0 <= i <= |nodes|
            invariant i < |nodes| ==> stack[|stack|-1] == nodes[i]
            invariant forall x :: x in unvisited ==> unchanged(x)
            invariant forall node :: node in visited ==> allocated(node)
            // invariant forall node :: node in visited ==> node.right == old(node.left) && node.left == old(node.right) && node.Valid()
            decreases unvisited
        {
            assert root.Valid();
            var current: TreeNode := stack[|stack|-1];
            AllDisjointMaint(stack, current);
            TreeUnionMaint(stack, current, unvisited);
            assert current in stack;
            assert current.Valid();
            ghost var oldstack := stack;
            stack := stack[..|stack|-1];
            assert stack == oldstack[..|oldstack|-1];
            assert forall x :: x in stack ==> x.Valid();
            ChildNodesAreValid(root, current);
            if current.right != null {
                assert current.right.repr <= root.repr;
                assert current.right in root.repr;
                assert current.right.Valid();
                ChildNodesAreValid(root, current.right);
                stack := stack + [current.right];
            }
            ghost var stacktemp := stack;
            if current.left != null {
                assert current.left.repr <= root.repr;
                assert current.left in root.repr;
                assert current.left.Valid();
                ChildNodesAreValid(root, current.left);
                stack :=  stack + [current.left];
            }
            assert old(root).Valid();
            var temp := current.left;
            current.left := current.right;
            current.right := temp;
            assert current.Valid();
            if current.left != null && current.right != null {
                assert [current.right]+[current.left] == [current.right, current.left];
                assert stacktemp ==oldstack[..|oldstack|-1]+ [current.right];
                assert stack == stacktemp + [current.left];
                assert stack == oldstack[..|oldstack|-1]+ [current.right, current.left];
            } else if current.left != null && current.right == null {
                assert stack == oldstack[..|oldstack|-1]+ [current.left];
            }else if current.left == null && current.right != null {
                assert stack == oldstack[..|oldstack|-1]+ [current.right];
            }else if current.left == null && current.right == null {
                assert stack == oldstack[..|oldstack|-1];
            }
            ValidSwappingStillValid(root, current);
            assert forall x :: x in stack ==> x.Valid();
            assert AllDisjoint(stack);
            assert temp == old(current.left);
            assert current.left == old(current.right) && current.right == old(current.left);
            visited := visited + {current};
            unvisited := unvisited - {current};
            i := i + 1;
        }
        assert visited == root.repr;
        return root;
    }
}