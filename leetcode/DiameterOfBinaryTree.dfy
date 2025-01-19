//https://leetcode.com/problems/diameter-of-binary-tree/description/

/*
function diameter(node: TreeNode | null): [number, number] {
  if(node == null) {
    return [-1,-1];
  }
  if(node.left == null && node.right == null) {
    return [0, 0];
  }
  let leftDiameter = diameter(node.left);
  let rightDiameter = diameter(node.right);
  let height = Math.max(leftDiameter[0],rightDiameter[0]) + 1;
  let dim = leftDiameter[0]+rightDiameter[0]+2;
  let maxDiameter = Math.max(leftDiameter[1], rightDiameter[1], dim);
  return [height, maxDiameter];
}

function diameterOfBinaryTree(root: TreeNode | null): number {
  return diameter(root)[1];
};
*/
include "../lib/seq.dfy"
include "../lib/binaryTree.dfy"
module TreeDiameter {
import opened BinaryTree
import opened SeqCustom


method TestPath() {
    var rootleaf := Node(4, Nil, Nil);
    var leaf := Node(3, Nil, Nil);
    var child := Node(2, Nil, leaf);
    var root := Node(1, child, rootleaf);

    var test := Node(10, rootleaf, rootleaf);
    //should this be allowed?
    assert isTreePath([rootleaf, root, rootleaf], rootleaf, rootleaf);
    // assert isPath([leaf, child, root, rootleaf]);
    assert !isTreePath([root, rootleaf], leaf, rootleaf);
    assert isTreePath([leaf, child, root], leaf, root);
    assert isTreePath([root, rootleaf], root, rootleaf);
    assert isTreePath([leaf, child, root, rootleaf], leaf, rootleaf);
    assert isDescTreePath([root, child, leaf], root, leaf);
    assert !isDescTreePath([root], root, leaf);
    assert isDescTreePath([root, rootleaf],root, rootleaf);
    // assert isTreePath([leaf], leaf, leaf);
    // assert isTreePath([child], child, child);
    // assert isTreePath([leaf,child], leaf, child);
    assert isTreePath([leaf,child,root], leaf, root);
    assert isTreePath([root,child,leaf], root, leaf);
}

ghost predicate isDiameter(path: seq<Tree>, start: Tree, end: Tree, root: Tree) {
    isPath(path, start, end, root) && forall paths: seq<Tree>, pathStart: Tree, pathEnd: Tree :: isPath(paths, pathStart, pathEnd, root) ==> |path| >= |paths|
}

ghost function tallestChild(root: Tree): Tree {
    if root == Nil then Nil else if root != Nil && TreeHeight(root.left) > TreeHeight(root.right) then root.left else root.right
}

lemma ascPathEndsAtRelativeRoot(start: Tree, end: Tree, path: seq<Tree>)
    requires start != Nil && end != Nil
    requires isAscTreePath(path, start, end)
    ensures isValidPath(path, end)
{
    if |path| ==1 {

    }else{
        AscPathChildren(path, start, end);
        AscTreePathNotNil(path, start, end);
        assert isChild(end, path[|path|-2]);
        assert path[|path|-2] in path;
        assert path[|path|-2] != Nil;
        assert path[|path|-2] in TreeSet(end);
        AscTreePathSplit(path, start, end);
        ascPathEndsAtRelativeRoot(start, path[|path|-2], path[..|path|-1]);
    }
}

lemma pathEndingAtRootAsc(root: Tree, start: Tree, end: Tree, path: seq<Tree>)
    requires root != Nil
    requires root in path && path[|path|-1] == root && end == root
    requires ChildrenAreSeparate(root)
    requires isPath(path, start, end, root)
    requires |path| >= 1
    decreases |path|
    ensures isAscTreePath(path, start, root)
{
    if |path| == 1 {
    }else {
        TreePathNotNil(path, start, root);
        TreePathsReverseAreTreePaths(path, start, end);
        ReverseIndexAll(path); 
        TreePathStartingAtRootIsDesc(reverse(path), end, start, root);
        DescPathIsAscPath(reverse(path), root, start);
        assert isAscTreePath(reverse(reverse(path)), start, root);
        reverseReverseIdempotent(path);
    }
}
// by a similar argument to pathStartingAtRootDesc
lemma nonAscendingContra(root: Tree, start: Tree, end: Tree, path: seq<Tree>)
    requires root != Nil
    requires root in path
    requires ChildrenAreSeparate(root)
    requires isPath(path, start, end, root)
    requires path[|path|-1] == root
    requires !isAscTreePath(path, start, end)
    requires !isDescTreePath(path, start, end)
    ensures false 
{
    assert end == root;
    if |path| == 1 {
        assert isAscTreePath(path, start, end);
        assert false;
    }else{
        if isChild(path[|path|-2], path[|path|-1]) {
            parentNotInTreeSet(path[|path|-2], root);
        }else if isChild(path[|path|-1], path[|path|-2]) {
            if |path| == 2 {

            }else{
                TreePathsAreTheSameAlt(path, start, end);
                TreePathSplit(path, start, end);
                distinctSplits(path);
                if isAscTreePath(path[..|path|-1], start, path[|path|-2]) {
                    assert path == path[..|path|-1]+[root];
                    AscTreePathNotNil(path[..|path|-1], start, path[|path|-2]);
                    AscTreePathAreTheSame(path[..|path|-1], start, path[|path|-2]);
                    assert isAscTreePathAlt(path, start, root);
                    AscTreePathAreTheSameAlt(path,start, root);
                    assert isAscTreePath(path, start, root);
                    assert false;
                } else if isDescTreePath(path[..|path|-1], start, path[|path|-2]) {
                    DescPathChildren(path[..|path|-1], start, path[|path|-2]);
                    assert isChild(path[|path|-3], path[|path|-2]); 
                    parentsAreTheSame(path[|path|-3], root, path[|path|-2]);
                    assert path[|path|-3] == root;
                    assert !distinct(path);
                    assert false;
                }else{
                    if isValidPath(path[..|path|-1], path[|path|-2]) {
                        nonAscendingContra(path[|path|-2], start, path[|path|-2], path[..|path|-1]);
                    }else{
                        var nextRoot :=path[|path|-2];
                        assert TreeSet(nextRoot) <= TreeSet(root);
                        TreePathsAreTheSameAlt(path, start, end);
                        var badnode: Tree, k: nat :| badnode in path[..|path|-1] && badnode !in TreeSet(nextRoot) && badnode in TreeSet(root) && k < |path|-2 && path[k] == badnode;
                        TreePathNotNil(path,start,end);
                        /*
                            Basically either the path is disconnected or root is in the path twice
                            We have some path in the alternate branch but it isn't connected
                        */
                        // forall i | 0 <= i < |path| - 1 
                        //     ensures isParentOrChild(path[i], path[i+1]) 
                        // {
                        //     assert isParentOrChild(path[i], path[i+1]);
                        // }
                        if nextRoot == root.left {
                            assert badnode in TreeSet(root.right);
                            nonAscendingContraHelpLeft(root, start, end, path, k, |path|-2, badnode);
                            assert false;
                        }else if nextRoot == root.right {
                            assert badnode in TreeSet(root.left);
                            nonAscendingContraHelpRight(root, start, end, path, k, |path|-2, badnode);
                            assert false;
                        }else {
                            assert false;
                        }
                    }
                }
            }
        }else{
            assert !isParentOrChild(path[|path|-2], path[|path|-1]);
            assert path == path[..|path|-2]+[path[|path|-2], root];
            TreePathsAreTheSameAlt(path, start, end);
            assert false;
        }

    }
}
 
lemma nonAscendingContraHelpRight(root: Tree, start: Tree, end: Tree, path: seq<Tree>, k: nat, i: nat, badnode: Tree)
    requires |path| > 2
    requires root != Nil
    requires root in path
    requires forall node :: node in path ==> node != Nil
    requires ChildrenAreSeparate(root)
    requires isPath(path, start, end, root)
    requires isTreePathAlt(path, start, end)
    requires path[|path|-1] == root
    requires isChild(path[|path|-1], path[|path|-2])
    requires root.right == path[|path|-2]
    requires !isAscTreePath(path, start, end)
    requires !isDescTreePath(path, start, end)
    requires !isValidPath(path[..|path|-1], path[|path|-2])
    requires k < i <= |path|-2
    requires path[i] in TreeSet(root.right)
    requires badnode in path[..|path|-1]
    requires badnode !in TreeSet(root.right) && badnode !in TreeSet(path[i]) && badnode in TreeSet(root) && badnode in TreeSet(root.left)
    requires k < |path|-2 && path[k] == badnode
    decreases i-k
    ensures false
{
    if root.left == Nil {

    }else{
        assert badnode in path;
        assert path[i] in path;
        TreeSetChildInTreeSet(root.right, path[i]);
        TreeSetChildInTreeSet(root.left, badnode);
        if isChild(badnode, path[k+1]) {
            assert path[k+1] in TreeSet(badnode);
            TreeSetChildInTreeSet(badnode, path[k+1]);
            assert path[k+1] in TreeSet(root.left);
            assert TreeSet(path[i]) <= TreeSet(root.right);
            assert TreeSet(path[i]) !! TreeSet(path[k+1]);
            nonAscendingContraHelpRight(root, start, end, path, k+1, i, path[k+1]);
        }else if isChild(path[k+1], badnode) {
            if path[k+1] in TreeSet(root.left) {
                nonAscendingContraHelpRight(root, start, end, path, k+1, i, path[k+1]);
            } else if path[k+1] in TreeSet(root) && path[k+1] !in TreeSet(root.left) && path[k+1] !in TreeSet(root.right) {
                assert path[k+1] == root;
            } else if path[k+1] in TreeSet(root.right) {
                assert badnode in TreeSet(path[k+1]);
                TreeSetChildInTreeSet(root.right, path[k+1]);
                assert TreeSet(path[k+1]) <= TreeSet(root.right);
                assert false;
            }else {

            }
        }else{

        }
    }
}

lemma nonAscendingContraHelpLeft(root: Tree, start: Tree, end: Tree, path: seq<Tree>, k: nat, i: nat, badnode: Tree)
    requires |path| > 2
    requires root != Nil
    requires root in path
    requires forall node :: node in path ==> node != Nil
    requires ChildrenAreSeparate(root)
    requires isPath(path, start, end, root)
    requires isTreePathAlt(path, start, end)
    requires path[|path|-1] == root
    requires isChild(path[|path|-1], path[|path|-2])
    requires root.left == path[|path|-2]
    requires !isAscTreePath(path, start, end)
    requires !isDescTreePath(path, start, end)
    requires !isValidPath(path[..|path|-1], path[|path|-2])
    requires k < i <= |path|-2
    requires path[i] in TreeSet(root.left)
    requires badnode in path[..|path|-1]
    requires badnode !in TreeSet(root.left) && badnode !in TreeSet(path[i]) && badnode in TreeSet(root) && badnode in TreeSet(root.right)
    requires k < |path|-2 && path[k] == badnode
    decreases i-k
    ensures false
{
    if root.left == Nil {

    }else{
        assert badnode in path;
        assert path[i] in path;
        TreeSetChildInTreeSet(root.left, path[i]);
        TreeSetChildInTreeSet(root.right, badnode);
        if k == |path|-3 {
            assert isParentOrChild(path[k], path[|path|-2]);
            assert path[k] !in TreeSet(path[|path|-2]);
            assert isChild(path[k], path[|path|-2]);
            parentsAreTheSame(path[|path|-3], root, path[|path|-2]);
        }else{
            if isChild(badnode, path[k+1]) {
                assert path[k+1] in TreeSet(badnode);
                TreeSetChildInTreeSet(badnode, path[k+1]);
                assert path[k+1] in TreeSet(root.right);
                assert TreeSet(path[i]) <= TreeSet(root.left);
                assert TreeSet(path[i]) !! TreeSet(path[k+1]);
                nonAscendingContraHelpLeft(root, start, end, path, k+1, i, path[k+1]);
            }else if isChild(path[k+1], badnode) {
                if path[k+1] in TreeSet(root.right) {
                    nonAscendingContraHelpLeft(root, start, end, path, k+1, i, path[k+1]);
                } else if path[k+1] in TreeSet(root) && path[k+1] !in TreeSet(root.left) && path[k+1] !in TreeSet(root.right) {
                    assert path[k+1] == root;
                } else if path[k+1] in TreeSet(root.left) {
                    assert badnode in TreeSet(path[k+1]);
                    TreeSetChildInTreeSet(root.left, path[k+1]);
                    assert false;
                }else {

                }
            }else{

            }
        }
    }
}

lemma {:vcs_split_on_every_assert} pathOptions(root: Tree, start: Tree, end: Tree, path: seq<Tree>)
    requires root != Nil
    requires root in path
    requires ChildrenAreSeparate(root)
    requires isPath(path, start, end, root)
    decreases |path|
    ensures isAscTreePath(path, start, end) || isDescTreePath(path, start, end) || exists i :: 0 < i < |path|-1 && path[i] == root && isAscTreePath(path[..(i+1)], start, root) && isDescTreePath(path[i..], root, end)
{
    if isAscTreePath(path, start, end) {

    } else if isDescTreePath(path, start, end) {

    }else{
        assert !isAscTreePath(path, start, end);
        assert !isDescTreePath(path, start, end);
        if path[0] == root {
            if |path| == 1 {
                assert exists i :: 0 <= i < |path| && path[i] == root && isAscTreePath(path[..(i+1)], start, root) && isDescTreePath(path[i..], root, end);
            }else{
                assert isAscTreePath(path[..(0+1)], start, root);
                pathStartingAtRootDesc(root, start, end, path);
                assert false;
            }
        }else if path[|path|-1] == root {
            // pathEndingAtRootAsc(root,start, end, path);
            nonAscendingContra(root,start, end, path);
            assert false;
        }else{
            assert root in path[1..];
            isPathSlices(path, start, end, root);
            var i :| 0 < i < |path|-1 && path[i] == root;
            // assert path == path[..(i+1)]+path[i+1..];
            assert path[..i+1][|path[..i+1]|-1] == root;
            assert path[i..][0] == root;
            assert isPath(path[..(i+1)], start, path[i], root);
            assert isPath(path[i..], root, end, root);
            pathStartingAtRootDesc(root, path[i], end, path[i..]);
            pathEndingAtRootAsc(root, start, path[i], path[..(i+1)]);
        }
    }
}

lemma {:vcs_split_on_every_assert} pathOptions2(root: Tree, start: Tree, end: Tree, path: seq<Tree>)
    requires root != Nil
    requires root !in path
    requires ChildrenAreSeparate(root)
    requires isPath(path, start, end, root)
    decreases |path|
    ensures isAscTreePath(path, start, end) || isDescTreePath(path, start, end) || exists childRoot: Tree, i :: 0 < i < |path|-1 && path[i] == childRoot && isAscTreePath(path[..(i+1)], start, childRoot) && isDescTreePath(path[i..], childRoot, end)
{
    if isAscTreePath(path, start, end) {

    } else if isDescTreePath(path, start, end) {

    }else{
        assert !isAscTreePath(path, start, end);
        assert !isDescTreePath(path, start, end);
        assert |path| > 1;
        if isChild(path[0], path[1]){ 
            //descending
            nonAscendingContra2(root, start, end, path, 2);

        }else{
            //ascending
            assert isChild(path[1], path[0]);
            ChildRootExists(root, start, end, path, 2);
            
        }
        assert exists childRoot: Tree, i :: 0 < i < |path|-1 && path[i] == childRoot && isAscTreePath(path[..(i+1)], start, childRoot) && isDescTreePath(path[i..], childRoot, end);

    }
}

lemma ChildRootExists(root: Tree, start: Tree, end: Tree, path: seq<Tree>, k: int)
    requires root != Nil
    requires root !in path
    requires 1 < k <= |path|
    requires ChildrenAreSeparate(root)
    requires isPath(path, start, end, root)
    requires isAscTreePath(path[..k], start, path[k-1])
    requires !isAscTreePath(path, start, end)
    requires !isDescTreePath(path, start, end)
    decreases |path|-k
    ensures exists childRoot: Tree, i :: 0 < i < |path|-1 && path[i] == childRoot && isAscTreePath(path[..(i+1)], start, childRoot) && isDescTreePath(path[i..], childRoot, end);
{

    if k == |path| {
        assert path[..k] == path;
        assert false;
    }else{
        TreePathNotNil(path, start, end);
        if isChild(path[k-1], path[k]) { 
            // DescPathChildrenAlt(path[(k-1)..][..2], path[k-1], end);
            assert isDescTreePath(path[(k-1)..][..2], path[k-1], path[k]);
            if |path[k-1..]| > 2 {
            AllDescPath(root, start, end, path, k, 2);

            }else{
                assert |path[k-1..]| == 2;
                assert path[(k-1)..] == path[(k-1)..][..2];
            }
        }else if isChild(path[k], path[k-1]) {
            AscTreePathAreTheSame(path[..k], start, path[k-1]);
            AscTreePathAreTheSameAlt(path[..(k+1)], start, path[k]);
            assert isAscTreePath(path[..(k+1)], start, path[k]);
            ChildRootExists(root, start, end, path, k+1);
        }else{
            TreePathsAreTheSameAlt(path, start, end);
            assert false;
        }
    }
}


lemma AllDescPathCont(root: Tree, start: Tree, end: Tree, path: seq<Tree>, k: int,  i: int)
    requires root != Nil
    requires root !in path
    requires 1 < k < |path|
    requires 1 < i < |path[(k-1)..]|
    requires ChildrenAreSeparate(root)
    requires isPath(path, start, end, root)
    requires isAscTreePath(path[..k], start, path[k-1])
    requires isChild(path[k-1], path[k])
    requires isDescTreePath(path[(k-1)..][..i], path[k-1], path[(k-1)..][i-1])
    requires !isAscTreePath(path, start, end)
    requires !isDescTreePath(path, start, end)
    ensures isDescTreePath(path[(k-1)..][..(i+1)], path[k-1], path[(k-1)..][i])
    decreases |path|-i
{
    TreePathNotNil(path, start, end);
    TreePathsAreTheSameAlt(path, start, end);
    DescPathChildren(path[(k-1)..][..i], path[k-1], path[(k-1)..][i-1]);
    if i == |path[(k-1)..]|-1 {
        if !isChild(path[(k-1)..][i-1], path[(k-1)..][i]) {
            assert isChild(path[(k-1)..][i], path[(k-1)..][i-1]);
        //     assert isChild(path[(k-1)], path[(k-1)..][i-2]);
        //     // assert isChild(path)
            if i == 2 {
                assert isChild(path[(k-1)], path[(k-1)..][i-1]);
                parentsAreTheSame(path[k-1], path[k-1..][i], path[(k-1)..][i-1]);
                assert false;
            }else{
                assert isChild(path[(k-1)..][i-2], path[(k-1)..][i-1]);
                parentsAreTheSame(path[(k-1)..][i-2], path[k-1..][i], path[(k-1)..][i-1]);
                assert false;

            assert false;
            }
            assert false;
        }
        assert path[k-1..] == path[(k-1)..][..(i+1)];
        DescPathChildrenAlt(path[(k-1)..][..(i+1)], path[k-1], path[(k-1)..][i]);
        assert isDescTreePath(path[(k-1)..][..(i+1)], path[k-1], path[(k-1)..][i]);
    }else{
        if !isChild(path[(k-1)..][i-1], path[(k-1)..][i]) {
            assert isChild(path[(k-1)..][i], path[(k-1)..][i-1]);
        //     assert isChild(path[(k-1)], path[(k-1)..][i-2]);
        //     // assert isChild(path)
            if i == 2 {
                assert isChild(path[(k-1)], path[(k-1)..][i-1]);
                parentsAreTheSame(path[k-1], path[k-1..][i], path[(k-1)..][i-1]);
                assert false;
            }else{
                assert isChild(path[(k-1)..][i-2], path[(k-1)..][i-1]);
                parentsAreTheSame(path[(k-1)..][i-2], path[k-1..][i], path[(k-1)..][i-1]);
                assert false;

            assert false;
            }
            assert false;
        }else{
            DescPathChildrenAlt(path[(k-1)..][..(i+1)], path[k-1], path[(k-1)..][i]);
            AllDescPathCont(root, start, end, path, k, i+1);
        }
    }
        // if i ==  {
        //     assert path[(k-1)..][i] == path[k-1];
        //     assert isChild(path[(k-1)..][i], path[(k-1)..][i+1]);
        // }else{
        //     // assert forall z :: 0 < z < i < |path[(k-1)..]|-1 ==> isChild(path[(k-1)..][z], path[(k-1)..][z+1]);
        //     if !isChild(path[(k-1)..][i], path[(k-1)..][i+1]) {
        //         assert isChild(path[(k-1)..][i+1], path[(k-1)..][i]);
        //         assert isChild(path[(k-1)..][i-1], path[(k-1)..][i]);

        //         assert false;
        //     }

        //     assert isChild(path[(k-1)..][i], path[(k-1)..][i+1]);
        // }
    // DescPathChildrenAlt(path[(k-1)..], path[k-1], end);
}

lemma AllDescPath(root: Tree, start: Tree, end: Tree, path: seq<Tree>, k: int,  i: int)
    requires root != Nil
    requires root !in path
    requires 1 < k < |path|
    requires 1 < i < |path[(k-1)..]|
    requires ChildrenAreSeparate(root)
    requires isPath(path, start, end, root)
    requires isAscTreePath(path[..k], start, path[k-1])
    requires isChild(path[k-1], path[k])
    requires isDescTreePath(path[(k-1)..][..i], path[k-1], path[(k-1)..][i-1])
    requires !isAscTreePath(path, start, end)
    requires !isDescTreePath(path, start, end)
    ensures isDescTreePath(path[(k-1)..], path[k-1], path[(k-1)..][|path[(k-1)..]|-1])
    decreases |path|-i
{

    TreePathNotNil(path, start, end);
    if i == |path[(k-1)..]|-1 {
        AllDescPathCont(root, start, end, path, k, i);
        assert path[k-1..] == path[(k-1)..][..(i+1)];

    }else{
        AllDescPathCont(root, start, end, path, k, i);
        AllDescPath(root, start, end, path, k, i+1);
    }
}

lemma nonAscendingContra2(root: Tree, start: Tree, end: Tree, path: seq<Tree>, i: int)
    requires root != Nil
    requires root !in path
    requires 1 < i <= |path|
    requires ChildrenAreSeparate(root)
    requires isPath(path, start, end, root)
    requires isDescTreePath(path[..i], start, path[i-1])
    requires !isAscTreePath(path, start, end)
    requires !isDescTreePath(path, start, end)
    decreases |path|-i
    ensures false 
{
    if i == |path| {
        assert path[..i] == path;

    }else{
        assert i < |path|;
        TreePathNotNil(path, start, end);
        if isChild(path[i-1], path[i]) { 
            //descending
            assert path[i] != Nil;
            assert path[..(i+1)] == path[..i]+[path[i]];
            DescPathChildren(path[..i], start, path[i-1]);
            DescPathChildrenAlt(path[..(i+1)], start, path[i]);
            assert isDescTreePath(path[..(i+1)], start, path[i]);
            nonAscendingContra2(root, start, end, path, i+1);

            assert false;
        }else if isChild(path[i], path[i-1]){
            //ascending
            DescPathChildren(path[..i], start, path[i-1]);
            assert isChild(path[i-2], path[i-1]);
            parentsAreTheSame(path[i], path[i-2], path[i-1]);
            assert false;
        }else{
            TreePathsAreTheSameAlt(path, start, end);
            assert false;
        }

    }
}


lemma rootPathAtMost3h(root: Tree, start: Tree, end: Tree, path: seq<Tree>, h: int)
    requires root != Nil
    requires root in path
    requires ChildrenAreSeparate(root)
    requires TreeHeight(root) == h
    requires isPath(path, start, end, root)
    ensures |path| <= 2 * h + 1
{
    assert start in TreeSet(root);
    assert end in TreeSet(root);
    RootBounded(root, h);
    pathOptions(root, start,end, path);

    if isDescTreePath(path, start, end) {
        descRoot(root, start, end, path);
        TreeHeightToDescTreePath(root, h);
        var maxend: Tree, maxpath: seq<Tree> :| (isLeaf(maxend) && maxend in TreeSet(root)) && isDescTreePath(maxpath, root, maxend) && |maxpath| == h+1 && isValidPath(maxpath, root) && distinct(maxpath);
        TreeHeightToMaxDescTreePath(root, h, maxend, maxpath);
        assert |path| <= |maxpath|;
    } else if isAscTreePath(path, start, end) {
        ascRoot(root, start, end, path);
        assert end == root;
        AscPathIsDescPath(path, start, root);
        ReverseIndexAll(path);
        assert |reverse(path)| == |path|;
        TreeHeightToDescTreePath(root, h);
        var maxend: Tree, maxpath: seq<Tree> :| (isLeaf(maxend) && maxend in TreeSet(root)) && isDescTreePath(maxpath, root, maxend) && |maxpath| == h+1 && isValidPath(maxpath, root) && distinct(maxpath);
        TreeHeightToMaxDescTreePath(root, h, maxend, maxpath);
        assert |path| <= |maxpath|;
    } else if i :| 0 < i < |path|-1 && path[i] == root && isAscTreePath(path[..(i+1)], start, root) && isDescTreePath(path[i..], root, end) {
        ReverseIndexAll(path[..(i+1)]);
        AscPathIsDescPath(path[..(i+1)],start, root);

        TreeHeightToDescTreePath(root, h);
        var maxend: Tree, maxpath: seq<Tree> :| (isLeaf(maxend) && maxend in TreeSet(root)) && isDescTreePath(maxpath, root, maxend) && |maxpath| == h+1 && isValidPath(maxpath, root) && distinct(maxpath);
        TreeHeightToMaxDescTreePath(root, h, maxend, maxpath);
        assert |(path[..(i+1)])| <= h+1;
        assert |path[i..]| <= h+1;
        assert |path| == |reverse(path[..(i+1)])| + |path[i+1..]|;
        assert |path| <= h+1 + h;
    }
}


lemma {:vcs_split_on_every_assert} pathsWithoutRoot(root: Tree, start: Tree, end: Tree, path: seq<Tree>, h: int)
    requires root != Nil
    requires root !in path
    requires |path| > 0
    requires ChildrenAreSeparate(root)
    requires TreeHeight(root) == h
    requires isPath(path, start, end, root)
    ensures isValidPath(path, root.left) || isValidPath(path, root.right)
{
    if root.right == Nil && root.left != Nil {
        assert isValidPath(path, root.left);
    } else if root.right != Nil && root.left == Nil {
        assert isValidPath(path, root.right);
    } else if root.right != Nil && root.left != Nil {
        if !isValidPath(path, root.left) && !isValidPath(path, root.right) {
            // var x,y, i: nat :| i < |path|-1 && x in TreeSet(root.right) && y in TreeSet(root.right) && x in path && y in path && path[i] == x && path[i+1] == y; 
            var badnode :| badnode in path && badnode !in TreeSet(root.left);
            var badnode2 :| badnode2 in path && badnode2 !in TreeSet(root.right);
            pathOptions2(root, start, end, path);
            if isAscTreePath(path, start, end) {
                AscPathChildrenTreeSet(path, start, end);
                if end in TreeSet(root.left) {
                    childrenInTreeSet(root.left, end, path);
                    assert badnode2 in TreeSet(end);
                }else{
                    childrenInTreeSet(root.right, end, path);
                    assert end in TreeSet(root.right);
                    assert badnode in TreeSet(end);
                }
                assert false;

            }else if isDescTreePath(path, start, end) {
                // DescTreePathSplitAltRev(path, start, end);
                DescPathChildrenTreeSet(path, start, end);
                if start in TreeSet(root.left) {
                    childrenInTreeSet(root.left, start, path);
                    assert badnode in TreeSet(root.left);
                }else{
                    assert start in TreeSet(root.right);
                    childrenInTreeSet(root.right, start, path);
                    assert badnode2 in TreeSet(root.right);
                }
                assert false;

            }else{
                var childRoot: Tree, i :| 0 < i < |path|-1 && path[i] == childRoot && isAscTreePath(path[..(i+1)], start, childRoot) && isDescTreePath(path[i..], childRoot, end);
                DescPathChildrenTreeSet(path[i..], childRoot, end);
                AscPathChildrenTreeSet(path[..(i+1)], start, childRoot);
                assert isValidPath(path, childRoot);
                if childRoot in TreeSet(root.left) {
                    childrenInTreeSet(root.left, childRoot, path);

                }else if childRoot in TreeSet(root.right) {
                    childrenInTreeSet(root.right, childRoot, path);
                }else{
                    assert childRoot == root;
                }

                assert false;
            }
            assert false;
        }
        // if x,y, i: nat :| i < |path|-1 && x in TreeSet(root.right) && y in TreeSet(root.right) && x in path && y in path && path[i] == x && path[i+1] == y {

        //     assert false;
        // }
    }
}

lemma {:verify false} DiameterAtMost3h(root: Tree, start: Tree, end: Tree, path: seq<Tree>, h: int)
    requires root != Nil
    requires root in path
    requires ChildrenAreSeparate(root)
    requires TreeHeight(root) == h
    requires isPath(path, start, end, root)
    ensures |path|  <= 2*h+1
{
    rootPathAtMost3h(root, start, end, path, h);
    // if root in path {
    //     rootPathAtMost3h(root, start, end, path, h);
    // }else{
    //     pathsWithoutRoot(root, start, end, path, h);
    //     if root.left != Nil {
    //         DiameterAtMost3h(root.left, start, end, path, h-1);
    //     }
    // }
}

lemma DescPathAllValid(path: seq<Tree>, start: Tree, end: Tree)
    requires isDescTreePath(path, start, end)
    ensures isValidPath(path, start)
{
    
}

lemma TreeSetTransitive(root: Tree, child: Tree, path: seq<Tree>) 
    requires root != Nil && child != Nil
    requires child in TreeSet(root)
    requires isValidPath(path, child)
    ensures isValidPath(path, root)
{

}

// lemma {:verify false} EDVP1(root: Tree, start: Tree, end: Tree, path: seq<Tree>)
//     requires root != Nil
//     requires ChildrenAreSeparate(root)
//     requires isPath(path, start, end, root)
//     requires start in TreeSet(root.left) && end in TreeSet(root.left)
//     ensures isValidPath(path, root.left)// && root !in path
// {
//     parentNotInTreeSet(root, root.left);
//     assert start != root;
//     assert end != root;

//     // pathOptions(root, start, end, path);
//     if isAscTreePath(path, start, end) {
//         AscPathIsDescPath(path, start, end);
//         assert isDescTreePath(reverse(path), end, start);
//         DescPathAllValid(reverse(path), start, end);
//         ReverseIndexAll(path);
//         assert isValidPath(path, end);
//         TreeSetChildInTreeSet(root.left, end);
//         TreeSetTransitive(root.left, end, path);
//         //assert root !in path;
//         assert isValidPath(path, root.left);
//     } else if isDescTreePath(path, start, end) {

//         isDescPathAndValidImpliesAllValid(path,start, end);
//         TreeSetTransitive(root.left, start, path);
//         // assert root !in path;
//         assert isValidPath(path, root.left);
//     } else {

//         //assert root !in path;
//         assert isValidPath(path, root.left);
//     }
// }

// lemma {:verify false} {:induction false} EndDeterminesValidPath(root: Tree, start: Tree, end: Tree, path: seq<Tree>)
//     requires root != Nil
//     requires ChildrenAreSeparate(root)
//     requires isPath(path, start, end, root)
//     ensures start in TreeSet(root.left) && end in TreeSet(root.left) ==> isValidPath(path, root.left) && root !in path
//     ensures start in TreeSet(root.right) && end in TreeSet(root.right) ==> isValidPath(path, root.right) && root !in path
//     ensures start in TreeSet(root.right) && end in TreeSet(root.left) ==> root in path;
//     ensures start in TreeSet(root.left) && end in TreeSet(root.right) ==> root in path;
// {

//     if start in TreeSet(root.left) && end in TreeSet(root.left)  {
//         assert isValidPath(path, root.left) && root !in path;
//     }else if start in TreeSet(root.right) && end in TreeSet(root.right)  {
//         assert isValidPath(path, root.right) && root !in path;
//     }else if start in TreeSet(root.right) && end in TreeSet(root.left) {
//         assert root in path;
//     }else if start in TreeSet(root.left) && end in TreeSet(root.right) {
//         assert root in path;
//     }
// }

// lemma {:verify false} {:induction false} AllDiameterAtMost3h(root: Tree, start: Tree, end: Tree, path: seq<Tree>, h: int)
//     requires root != Nil
//     requires ChildrenAreSeparate(root)
//     requires TreeHeight(root) == h
//     requires isValidPath(path, root.left) || isValidPath(path, root.right)
//     requires isDiameter(path, start, end, root)
//     ensures |path|  <= 2*h+1
// {
//     //rootPathAtMost3h(root, start, end, path, h);
//     EndDeterminesPath(path,start,end);
//     if end in TreeSet(start.left) {
//         assert isValidPath(path, root.left);
//     }else if end in TreeSet(start.left) {
//         assert isValidPath(path, root.left);
//     }
// }

lemma {:verify false} DiameterIncludesRootOrInDeepestTree(root: Tree, start: Tree, end: Tree, path: seq<Tree>)
    requires root != Nil
    requires isDiameter(path, start, end, root)
    ensures root in path || (root !in path && isValidPath(path, tallestChild(root)))
{
    if root in path {

    }else{

    }
}

lemma childHeightIsLessThanPath(root: Tree, child:Tree, h: int, end: Tree)
    requires root != Nil
    requires ChildrenAreSeparate(root)
    requires h == TreeHeight(root)
    requires isChild(root, child)
    requires TreeHeight(child) <= h-1
    ensures forall rootedPath: seq<Tree>, anyend: Tree :: isDescTreePath(rootedPath, child, anyend)  && isValidPath(rootedPath, child) && distinct(rootedPath) ==> |rootedPath| <= h
{
    forall rootedPath: seq<Tree>, anyend: Tree | isDescTreePath(rootedPath, child, anyend)  && isValidPath(rootedPath, child) && distinct(rootedPath)
        ensures |rootedPath| <= h
    {
        if |rootedPath| <= h {

        }else if |rootedPath| > h {
            TreeHeightMax(child);
            EndDeterminesPath(rootedPath, child, anyend);
            if anyend in TreeSet(child.left) {
                if child.left == Nil {
                    assert false;
                }else{
                    childHeightIsLessThanPath(child, child.left, TreeHeight(child), anyend);
                    assert forall childPaths: seq<Tree>, anyend: Tree ::  isDescTreePath(childPaths, child.left, anyend)  && isValidPath(childPaths, child.left) && distinct(childPaths) ==> |childPaths| <= TreeHeight(child);
                    assert rootedPath[1] == child.left;
                    assert rootedPath == [child] + rootedPath[1..];
                    isDescPathAndValidImpliesAllValid(rootedPath,child,anyend);
                    assert isDescTreePath(rootedPath[1..], child.left, anyend);
                    assert isValidPath(rootedPath[1..], child.left);
                    assert |rootedPath[1..]| <= TreeHeight(child);
                    assert false;
                }

            }else if anyend in TreeSet(child.right) {
                if child.right == Nil {
                    assert false;
                }else{

                    childHeightIsLessThanPath(child, child.right, TreeHeight(child), anyend);
                    assert forall childPaths: seq<Tree>, anyend: Tree ::  isDescTreePath(childPaths, child.right, anyend)  && isValidPath(childPaths, child.right) && distinct(childPaths) ==> |childPaths| <= TreeHeight(child);
                    isDescPathAndValidImpliesAllValid(rootedPath,child,anyend);
                    assert isDescTreePath(rootedPath[1..], child.right, anyend);
                    assert false;
                }
            }else{
                assert anyend !in TreeSet(child.right) && anyend !in TreeSet(child.left);
                if anyend == child {

                }else{
                    assert anyend !in TreeSet(child);
                    assert false;
                }
            }

        }
    }
}

lemma TreeHeightToMaxDescTreePath(root: Tree, h: int, end: Tree, path: seq<Tree>) 
    requires root != Nil
    requires ChildrenAreSeparate(root)
    requires h == TreeHeight(root)
    requires end != Nil  && end in TreeSet(root)
    requires isDescTreePath(path, root, end)
    requires |path| == h+1
    requires isValidPath(path, root) 
    requires distinct(path)
    ensures forall rootedPath: seq<Tree>, anyend: Tree :: isDescTreePath(rootedPath, root, anyend)  && isValidPath(rootedPath, root) && distinct(rootedPath) ==> |rootedPath| <= |path|
    
{
    TreeHeightMax(root);
    RootBounded(root, h);
    forall rootedPath: seq<Tree>, anyend: Tree | isDescTreePath(rootedPath, root, anyend)  && isValidPath(rootedPath, root) && distinct(rootedPath)
        ensures |rootedPath| <= |path|
    {
        assert rootedPath[0] == root;
        assert |rootedPath| >= 1;
        if |rootedPath| == 1 {

        }else{
            EndDeterminesPath(rootedPath, root, anyend);
            if anyend in TreeSet(root.left) {
                childHeightIsLessThanPath(root, root.left, h, anyend);
                assert forall childPaths: seq<Tree>, anyend: Tree ::  isDescTreePath(childPaths, root.left, anyend)  && isValidPath(childPaths, root.left) && distinct(childPaths) ==> |childPaths| <= h;
                isDescPathAndValidImpliesAllValid(rootedPath,root,anyend);
                assert isDescTreePath(rootedPath[1..], root.left, anyend);
                assert |rootedPath[1..]| <= h;
                assert |rootedPath| <= h+1;
            }else if anyend in TreeSet(root.right) {
                childHeightIsLessThanPath(root, root.right, h, anyend);
                isDescPathAndValidImpliesAllValid(rootedPath,root,anyend);
                assert isDescTreePath(rootedPath[1..], root.right, anyend);
                assert |rootedPath[1..]| <= h;
                assert |rootedPath| <= h+1;
            }else{
                if anyend == root {

                }else{
                    assert anyend !in TreeSet(root);
                    assert false;
                }
            }
        }
    }
   
}

lemma {:induction false} rootPathMaxLeft(root: Tree, start: Tree, end: Tree, path: seq<Tree>, h: int)
    requires root != Nil
    requires root in path
    requires ChildrenAreSeparate(root)
    requires TreeHeight(root) == h
    requires isPath(path, start, end, root)
    // ensures |path| <= 2 * h + 1
    requires root.left != Nil
    requires root.right == Nil
    requires |path| == 1+TreeHeight(root)
    ensures largestRootedPath(path, root)
{
    TreePathNotNil(path, start, end);
    forall astart: Tree, aend: Tree, paths: seq<Tree> | root in paths && distinct(paths) && isTreePath(paths, astart, aend) && isValidPath(paths, root)
        ensures 1+TreeHeight(root) >= |paths|
    {
        pathOptions(root, start, end, path);
        // pathOptions(root, astart, aend, paths);
        if isAscTreePath(path, start, end) {
            ascRoot(root, start, end, path);
            ReverseIndexAll(path);
            AscPathIsDescPath(path, start, root);
            TreeHeightToMaxDescTreePath(root, h, start, reverse(path));
            pathOptions(root, astart, aend, paths);
            if isAscTreePath(paths, astart, aend) {
                ascRoot(root, astart, aend, paths);
                ReverseIndexAll(paths);
                AscPathIsDescPath(paths, astart, root);

                assert 1+TreeHeight(root) >= |paths|;
            }else if isDescTreePath(paths, astart, aend) {
                descRoot(root, astart, aend, paths);

                assert 1+TreeHeight(root) >= |paths|;
            }else{
                var i :| 0 < i < |paths|-1 && paths[i] == root && isAscTreePath(paths[..(i+1)], astart, root) && isDescTreePath(paths[i..], root, aend);
                assert paths[i-1] == paths[i+1] by {
                    AscPathChildren(paths[..(i+1)], astart, root);
                    assert isChild(paths[i], paths[i-1]);
                    assert isChild(paths[i], paths[i+1]);
                    TreePathNotNil(paths, astart, aend);
                    assert paths[i-1] != Nil;
                    assert paths[i+1] != Nil;
                }
                assert false;
                // assert 1+TreeHeight(root) >= |paths|;
            }

            assert 1+TreeHeight(root) >= |paths|;
        } else if isDescTreePath(path, start, end) {
            descRoot(root, start, end, path);
            TreeHeightToMaxDescTreePath(root, h, end, path);
            pathOptions(root, astart, aend, paths);
            if isAscTreePath(paths, astart, aend) {
                ascRoot(root, astart, aend, paths);
                ReverseIndexAll(paths);
                AscPathIsDescPath(paths, astart, root);

                assert 1+TreeHeight(root) >= |paths|;
            }else if isDescTreePath(paths, astart, aend) {
                descRoot(root, astart, aend, paths);

                assert 1+TreeHeight(root) >= |paths|;
            }else{
                var i :| 0 < i < |paths|-1 && paths[i] == root && isAscTreePath(paths[..(i+1)], astart, root) && isDescTreePath(paths[i..], root, aend);
                assert paths[i-1] == paths[i+1] by {
                    TreePathNotNil(paths, astart, aend);
                    assert paths[i-1] != Nil;
                    assert paths[i+1] != Nil;
                    AscPathChildren(paths[..(i+1)], astart, root);
                    assert isChild(paths[i], paths[i-1]);
                    assert isChild(paths[i], paths[i+1]);
                }
                assert false;
                // assert 1+TreeHeight(root) >= |paths|;
            }
            assert 1+TreeHeight(root) >= |paths|;
        }else{
            var i :| 0 < i < |path|-1 && path[i] == root && isAscTreePath(path[..(i+1)], start, root) && isDescTreePath(path[i..], root, end);
            AscPathChildren(path[..(i+1)], start, root);
            assert isChild(path[i], path[i-1]);
            assert isChild(path[i], path[i+1]);
            assert false;
        }
    }
}

lemma {:induction false}  rootPathMaxRight(root: Tree, start: Tree, end: Tree, path: seq<Tree>, h: int)
    requires root != Nil
    requires root in path
    requires ChildrenAreSeparate(root)
    requires TreeHeight(root) == h
    requires isPath(path, start, end, root)
    // ensures |path| <= 2 * h + 1
    requires root.left == Nil
    requires root.right != Nil
    requires |path| == 1+TreeHeight(root)
    ensures largestRootedPath(path, root)
{
    TreePathNotNil(path, start, end);
    forall astart: Tree, aend: Tree, paths: seq<Tree> | root in paths && distinct(paths) && isTreePath(paths, astart, aend) && isValidPath(paths, root)
        ensures 1+TreeHeight(root) >= |paths|
    {
        pathOptions(root, start, end, path);
        // pathOptions(root, astart, aend, paths);
        if isAscTreePath(path, start, end) {
            ascRoot(root, start, end, path);
            ReverseIndexAll(path);
            AscPathIsDescPath(path, start, root);
            TreeHeightToMaxDescTreePath(root, h, start, reverse(path));
            pathOptions(root, astart, aend, paths);
            if isAscTreePath(paths, astart, aend) {
                ascRoot(root, astart, aend, paths);
                ReverseIndexAll(paths);
                AscPathIsDescPath(paths, astart, root);

                assert 1+TreeHeight(root) >= |paths|;
            }else if isDescTreePath(paths, astart, aend) {
                descRoot(root, astart, aend, paths);

                assert 1+TreeHeight(root) >= |paths|;
            }else{
                var i :| 0 < i < |paths|-1 && paths[i] == root && isAscTreePath(paths[..(i+1)], astart, root) && isDescTreePath(paths[i..], root, aend);
                assert paths[i-1] == paths[i+1] by {
                    TreePathNotNil(paths, astart, aend);
                    assert paths[i-1] != Nil;
                    assert paths[i+1] != Nil;
                    AscPathChildren(paths[..(i+1)], astart, root);
                    assert isChild(paths[i], paths[i-1]);
                    assert isChild(paths[i], paths[i+1]);
                }
                assert false;
                // assert 1+TreeHeight(root) >= |paths|;
            }

            assert 1+TreeHeight(root) >= |paths|;
        } else if isDescTreePath(path, start, end) {
            descRoot(root, start, end, path);
            TreeHeightToMaxDescTreePath(root, h, end, path);
            pathOptions(root, astart, aend, paths);
            if isAscTreePath(paths, astart, aend) {
                ascRoot(root, astart, aend, paths);
                ReverseIndexAll(paths);
                AscPathIsDescPath(paths, astart, root);

                assert 1+TreeHeight(root) >= |paths|;
            }else if isDescTreePath(paths, astart, aend) {
                descRoot(root, astart, aend, paths);

                assert 1+TreeHeight(root) >= |paths|;
            }else{
                var i :| 0 < i < |paths|-1 && paths[i] == root && isAscTreePath(paths[..(i+1)], astart, root) && isDescTreePath(paths[i..], root, aend);
                assert paths[i-1] == paths[i+1] by {
                    TreePathNotNil(paths, astart, aend);
                    assert paths[i-1] != Nil;
                    assert paths[i+1] != Nil;
                    AscPathChildren(paths[..(i+1)], astart, root);
                    assert isChild(paths[i], paths[i-1]);
                    assert isChild(paths[i], paths[i+1]);
                }
                assert false;
                // assert 1+TreeHeight(root) >= |paths|;
            }
            assert 1+TreeHeight(root) >= |paths|;
        }else{
            var i :| 0 < i < |path|-1 && path[i] == root && isAscTreePath(path[..(i+1)], start, root) && isDescTreePath(path[i..], root, end);
            assert path[i] == path[i+1] by {
            AscPathChildren(path[..(i+1)], start, root);
            assert isChild(path[i], path[i-1]);
            assert isChild(path[i], path[i+1]);

            }
            assert false;
        }
    }
}

lemma {:induction false}  rootPathMax(root: Tree, start: Tree, end: Tree, path: seq<Tree>, h: int)
    requires root != Nil
    requires root in path
    requires ChildrenAreSeparate(root)
    requires TreeHeight(root) == h
    requires isPath(path, start, end, root)
    // ensures |path| <= 2 * h + 1
    requires root.left == Nil && root.right == Nil ==> |path| == 1
    requires root.left != Nil && root.right == Nil ==> |path| == 1+TreeHeight(root)
    requires root.left == Nil && root.right != Nil ==> |path| == 1+TreeHeight(root)
    requires root.left != Nil && root.right != Nil ==> |path| == 3+TreeHeight(root.right)+TreeHeight(root.left)
    ensures largestRootedPath(path, root)
{
    TreePathNotNil(path, start, end);
    if root.left == Nil && root.right == Nil {
        forall start: Tree, end: Tree, paths: seq<Tree> | root in paths && distinct(paths) && isTreePath(paths, start, end) && isValidPath(paths, root)
            ensures |[root]| >= |paths|
        {
           if |paths| > 1 {
            if paths[0] != root {
                    assert paths[0] !in TreeSet(root);

            }else{
                if paths[1] != root{
                    assert paths[1] !in TreeSet(root);
                }else{
                    assert paths[0] == paths[1];

                }
            }

            assert false;
           } 
        }
        assert largestRootedPath([root], root);
    }

    if root.left != Nil && root.right == Nil {
        // TreeHeightToDescTreePath(root, h);
        // var lpath :=
        //var  lend: Tree, lpath: seq<Tree> :| (isLeaf(lend) && lend in TreeSet(root))  && isDescTreePath(lpath, root, lend) && |lpath| == h+1 && isValidPath(lpath, root) && distinct(lpath);
        rootPathMaxLeft(root, start, end, path, h);
    }

    if root.left == Nil && root.right != Nil {
        rootPathMaxRight(root,start, end, path, h);
    }

    if root.left != Nil && root.right != Nil {
        // TreeHeightToDescTreePath(root, h);
        forall astart: Tree, aend: Tree, paths: seq<Tree> | root in paths && distinct(paths) && isTreePath(paths, astart, aend) && isValidPath(paths, root)
            ensures 3+TreeHeight(root.right)+TreeHeight(root.left) >= |paths|
        {
            pathOptions(root, start, end, path);
            if isAscTreePath(path, start, end) {
                ascRoot(root, start, end, path);
                ReverseIndexAll(path);
                AscPathIsDescPath(path, start, root);
                TreeHeightToDescTreePath(root, h);
                var dend: Tree, dpath: seq<Tree> :| (isLeaf(dend) && dend in TreeSet(root))  && isDescTreePath(dpath, root, dend) && |dpath| == h+1 && isValidPath(dpath, root) && distinct(dpath);
                TreeHeightToMaxDescTreePath(root, h, dend, dpath);
                assert false;

             //assert 3+TreeHeight(root.right)+TreeHeight(root.left) >= |paths|;
            } else if isDescTreePath(path, start, end) {
                descRoot(root, start, end, path);
                TreeHeightToDescTreePath(root, h);
                var dend: Tree, dpath: seq<Tree> :| (isLeaf(dend) && dend in TreeSet(root))  && isDescTreePath(dpath, root, dend) && |dpath| == h+1 && isValidPath(dpath, root) && distinct(dpath);
                TreeHeightToMaxDescTreePath(root, h, dend, dpath);
                assert false;

            }else{
                var i :| 0 < i < |path|-1 && path[i] == root && isAscTreePath(path[..(i+1)], start, root) && isDescTreePath(path[i..], root, end);
                pathOptions(root, astart, aend, paths);
                if isAscTreePath(paths, astart, aend) {
                    TreeHeightToDescTreePath(root, h);
                    var dend: Tree, dpath: seq<Tree> :| (isLeaf(dend) && dend in TreeSet(root))  && isDescTreePath(dpath, root, dend) && |dpath| == h+1 && isValidPath(dpath, root) && distinct(dpath);
                    TreeHeightToMaxDescTreePath(root, h, dend, dpath);
                    ascRoot(root, astart, aend, paths);
                    ReverseIndexAll(paths);
                    AscPathIsDescPath(paths, astart, root);
                    assert isDescTreePath(reverse(paths), root, astart);
                    assert |paths| <= |dpath|;
                    assert 3+TreeHeight(root.right)+TreeHeight(root.left) > |dpath|;

                } else if isDescTreePath(paths, astart, aend) {
                    descRoot(root, astart, aend, paths);
                    TreeHeightToDescTreePath(root, h);
                    var dend: Tree, dpath: seq<Tree> :| (isLeaf(dend) && dend in TreeSet(root))  && isDescTreePath(dpath, root, dend) && |dpath| == h+1 && isValidPath(dpath, root) && distinct(dpath);
                    TreeHeightToMaxDescTreePath(root, h, dend, dpath);
                    assert isDescTreePath(paths, root, aend);
                    assert |paths| <= |dpath|;
                    assert 3+TreeHeight(root.right)+TreeHeight(root.left) > |dpath|;

                    assert 3+TreeHeight(root.right)+TreeHeight(root.left) >= |paths|;
                }else{
                    var j :| 0 < j < |paths|-1 && paths[j] == root && isAscTreePath(paths[..(j+1)], astart, root) && isDescTreePath(paths[j..], root, aend);
                    TreePathNotNil(paths, astart, aend);
                    rootPathAtMost3h(root, astart, aend, paths, h);
                    DescTreePathToPath(paths[(j+1)..], paths[j+1], aend);
                    AscTreePathSplit(paths[..(j+1)], astart, root);
                    assert paths[..(j+1)][..|paths[..(j+1)]|-1] == paths[..j];
                    assert isAscTreePath(paths[..j], astart, paths[j-1]);
                    AscTreePathToPath(paths[..j], astart, paths[j-1]);
                    pathsWithoutRoot(root, astart, paths[j-1], paths[..j], h);
                    pathsWithoutRoot(root, paths[j+1], aend, paths[(j+1)..], h);
                    if isValidPath(paths[(j+1)..], root.left) && isValidPath(paths[..j], root.left) {
                        assert paths[j-1] == paths[j+1] by {
                            AscPathChildren(paths[..(j+1)], astart, paths[j]);
                            assert isChild(paths[j], paths[j-1]);
                            assert isChild(paths[j], paths[j+1]);
                        }
                        assert false;
                    } else if isValidPath(paths[(j+1)..], root.right) && isValidPath(paths[..j], root.right) {
                        assert paths[j-1] == paths[j+1] by {
                            AscPathChildren(paths[..(j+1)], astart, paths[j]);
                            assert isChild(paths[j], paths[j-1]);
                            assert isChild(paths[j], paths[j+1]);
                        }
                        assert false;
                    } else if isValidPath(paths[(j+1)..], root.left) && isValidPath(paths[..j], root.right) {
                        assert TreeHeight(root.left) <= h-1;
                        assert TreeHeight(root.right) <= h-1;

                        TreeHeightToDescTreePath(root.left, TreeHeight(root.left));
                        var dend: Tree, dpath: seq<Tree> :| (isLeaf(dend) && dend in TreeSet(root.left))  && isDescTreePath(dpath, root.left, dend) && |dpath| == TreeHeight(root.left)+1 && isValidPath(dpath, root.left) && distinct(dpath);
                        TreeHeightToMaxDescTreePath(root.left, TreeHeight(root.left), dend, dpath);
                        assert isDescTreePath(paths[j+1..], root.left, aend);
                        assert |paths[j+1..]| <= TreeHeight(root.left)+1;


                        TreeHeightToDescTreePath(root.right, TreeHeight(root.right));
                        var rend: Tree, rpath: seq<Tree> :| (isLeaf(rend) && rend in TreeSet(root.right))  && isDescTreePath(rpath, root.right, rend) && |rpath| == TreeHeight(root.right)+1 && isValidPath(rpath, root.right) && distinct(rpath);
                        TreeHeightToMaxDescTreePath(root.right, TreeHeight(root.right), rend, rpath);

                        ReverseIndexAll(paths[..j]);
                        assert paths[j-1] == root.right by {
                            AscPathChildren(paths[..(j+1)], astart, paths[j]);
                            assert isChild(root, paths[j-1]);
                        }
                        AscPathIsDescPath(paths[..j], astart, root.right);
                        assert isDescTreePath(reverse(paths[..j]), root.right, astart);
                        assert |paths[..j]| <= TreeHeight(root.right)+1;
                        assert paths == paths[..j]+[root]+paths[j+1..];
                        assert |paths| <= TreeHeight(root.right)+1 + 1 + TreeHeight(root.left)+1;

                        assert 3+TreeHeight(root.right)+TreeHeight(root.left) >= |paths|;
                    } else if isValidPath(paths[(j+1)..], root.right) && isValidPath(paths[..j], root.left) {
                        assert TreeHeight(root.left) <= h-1;
                        assert TreeHeight(root.right) <= h-1;

                        TreeHeightToDescTreePath(root.right, TreeHeight(root.right));
                        var dend: Tree, dpath: seq<Tree> :| (isLeaf(dend) && dend in TreeSet(root.right))  && isDescTreePath(dpath, root.right, dend) && |dpath| == TreeHeight(root.right)+1 && isValidPath(dpath, root.right) && distinct(dpath);
                        TreeHeightToMaxDescTreePath(root.right, TreeHeight(root.right), dend, dpath);
                        assert isDescTreePath(paths[j+1..], root.right, aend);
                        assert |paths[j+1..]| <= TreeHeight(root.right)+1;


                        TreeHeightToDescTreePath(root.left, TreeHeight(root.left));
                        var rend: Tree, rpath: seq<Tree> :| (isLeaf(rend) && rend in TreeSet(root.left))  && isDescTreePath(rpath, root.left, rend) && |rpath| == TreeHeight(root.left)+1 && isValidPath(rpath, root.left) && distinct(rpath);
                        TreeHeightToMaxDescTreePath(root.left, TreeHeight(root.left), rend, rpath);

                        ReverseIndexAll(paths[..j]);
                        assert paths[j-1] == root.left by {
                            AscPathChildren(paths[..(j+1)], astart, paths[j]);
                            assert isChild(root, paths[j-1]);
                        }
                        AscPathIsDescPath(paths[..j],  astart, root.left);
                        assert isDescTreePath(reverse(paths[..j]), root.left, astart);
                        assert |paths[..j]| <= TreeHeight(root.left)+1;
                        assert paths == paths[..j]+[root]+paths[j+1..];
                        assert |paths| <= TreeHeight(root.right)+1 + 1 + TreeHeight(root.left)+1;

                        assert 3+TreeHeight(root.right)+TreeHeight(root.left) >= |paths|;
                    }else{
                        assert false;
                    }
                    assert 3+TreeHeight(root.right)+TreeHeight(root.left) >= |paths|;
                }

            }
             assert 3+TreeHeight(root.right)+TreeHeight(root.left) >= |paths|;
        }
    }
}

lemma BothCases(root: Tree, left: Tree, right: Tree, h1: int, h2: int)
    requires root != Nil && left != Nil && right != Nil
    requires ChildrenAreSeparate(root)
    requires root.left == left && root.right == right
    requires TreeHeight(root.left) == h1
    requires TreeHeight(root.right) == h2
    ensures exists start: Tree, end: Tree, path: seq<Tree> :: root in path && isTreePath(path, start, end) && |path| == h1+h2 + 3 && isValidPath(path, root) && distinct(path);
{

        TreeHeightToDescTreePath(right, h2);
        var rpath: seq<Tree>, rend: Tree :| (isLeaf(rend) && rend in TreeSet(right))  && isDescTreePath(rpath, right, rend) && |rpath| == h2+1 && isValidPath(rpath, right) && distinct(rpath);
        assert rend in TreeSet(right);
        assert isDescTreePath([root]+rpath, root, rend);
        DescTreePathToPath(rpath, root.right, rend);
        TreeHeightToDescTreePath(left, h1);
        var lpath: seq<Tree>, lend: Tree :| (isLeaf(lend) && lend in TreeSet(left))  && isDescTreePath(lpath, left, lend) && |lpath| == h1+1 && isValidPath(lpath, left) && distinct(lpath);
        assert isDescTreePath([root]+lpath, root, lend);
        DescTreePathToPath(lpath, root.left, lend);
        
        parentNotInTreeSet(root, left);
        parentNotInTreeSet(root, right);
        assert root !in TreeSet(left);
        assert root !in TreeSet(right);
        assert lend in TreeSet(left);
        distincts([root], lpath);
        assert distinct([root]+lpath);
        reverseDistinct([root]+lpath);
        assert rend != lend;
        DescPlusDesc([root]+rpath, lend, root, [root]+lpath, rend);
        assert isTreePath(reverse([root]+lpath)+rpath, lend, rend);
        assert |[root]+lpath| == h1+2;
        ReverseIndexAll([root]+lpath);
        assert |[root]+lpath| == h1+2;
        assert |reverse([root]+lpath)+rpath| == h1+h2+3;
        distincts(reverse([root]+lpath), rpath);
}

ghost predicate largestPath(path: seq<Tree>, root: Tree) {
    forall start: Tree, end: Tree, paths: seq<Tree> :: distinct(paths) && isTreePath(paths, start, end) && isValidPath(paths, root) ==> |path| >= |paths|
}

ghost function allPaths(root: Tree): iset<seq<Tree>> {
    iset start: Tree, end: Tree, paths: seq<Tree> | distinct(paths) && isTreePath(paths, start, end) && isValidPath(paths, root) :: paths
}

ghost function allRootedPaths(root: Tree): iset<seq<Tree>> {
    iset start: Tree, end: Tree, paths: seq<Tree> | root in paths && distinct(paths) && isTreePath(paths, start, end) && isValidPath(paths, root) :: paths
}

lemma pathSums(root: Tree)
    requires root != Nil
    requires ChildrenAreSeparate(root)
    ensures allPaths(root) == allRootedPaths(root)+allPaths(root.left)+allPaths(root.right)
{
    forall path | path in allPaths(root)
        ensures path in allRootedPaths(root)+allPaths(root.left)+allPaths(root.right)
    {
        if root in path {
            assert path in allRootedPaths(root);
        }else{
            pathsWithoutRoot(root, path[0], path[|path|-1], path, TreeHeight(root));
        }
    }

    forall path | path in allRootedPaths(root)+allPaths(root.left)+allPaths(root.right)
        ensures path in allPaths(root)
    {
        
    }
}

ghost predicate largestRootedPath(path: seq<Tree>, root: Tree) {
    root in path && isPath(path, path[0], path[|path|-1], root) && forall start: Tree, end: Tree, paths: seq<Tree> :: root in paths && distinct(paths) && isTreePath(paths, start, end) && isValidPath(paths, root) ==> |path| >= |paths|
}

lemma NullLargest(path: seq<Tree>, root: Tree) 
    requires root == Nil
    requires path == []
    ensures largestPath(path, root)
{
    forall start: Tree, end: Tree, paths: seq<Tree> | distinct(paths) && isTreePath(paths, start, end) && isValidPath(paths, root) 
        ensures |path| >= |paths|
    {
        if |paths| > 0 {
            assert paths[0] != Nil;
            assert TreeSet(root) == {};
            assert paths[0] in TreeSet(root);
            assert false;
        }

    }
}

ghost predicate largestPathStart(path: seq<Tree>, root: Tree) {
    forall end: Tree, paths: seq<Tree> :: distinct(paths) && isTreePath(paths, root, end)  && isValidPath(paths, root) ==> |path| >= |paths|
}

lemma lpR(root: Tree)
    requires root != Nil && root.left == Nil && root.right == Nil
    ensures largestPath([root], root)
{
    assert distinct([root]);
    assert isValidPath([root], root);
    assert isTreePath([root], root, root);

    forall start: Tree, end: Tree, paths: seq<Tree> | distinct(paths) && isTreePath(paths, start, end) && isValidPath(paths, root)
     ensures |[root]| >= |paths|
    {
        if |paths| > 1 {
            assert paths[0] != paths[1];
            if isChild(paths[0], paths[1]) {
                if paths[0] == root {
                    assert false;
                }else if paths[1] == root {
                    parentNotInTreeSet(paths[0], root);
                    assert false;
                }else{
                    assert paths[0] !in TreeSet(root);
                }
            } else if isChild(paths[1], paths[0]) {
                if paths[0] == root {
                    parentNotInTreeSet(paths[1], root);
                    assert false;
                }else if paths[1] == root {
                    parentNotInTreeSet(paths[0], root);
                    assert false;
                }
            }else {
                assert false;
            }
        }else if |paths| == 0{

        }else{

        }
    }

}


// https://www.youtube.com/watch?v=2PFl93WM_ao
//Property I 
//Deepest branch contain the maximal diameter

//Suppose c1 does not contain the diameter.
//d_1 = D(c1)
//d_2 = =D(c_i)
//d1+d2+2 >= d2
//d1 = d2 + delta where delta >=0
//d1 + d2 +2 == d2+delta +d2+2 == 2*d2+delta+2 > 2*d2
//How many diameters can be in a tree with n nodes?
//Count the number of diametes in T?

lemma LargestRootBoth(root: Tree, h: int, 
leftPath: seq<Tree>, rightPath: seq<Tree>, 
leftWidth: int, rightWidth: int, 
diameter: int, rootPath: seq<Tree>, rootDim: int, greatestPath: seq<Tree>, start: Tree, end: Tree)
    requires ChildrenAreSeparate(root)
    requires root != Nil
    requires h == TreeHeight(root)
    requires largestPath(leftPath, root.left)
    requires largestPath(rightPath, root.right)
    requires largestRootedPath(rootPath, root)

    requires distinct(rootPath)
    requires root in rootPath
    requires rootDim == |rootPath|-1
    requires |rootPath| == 3+TreeHeight(root.right)+TreeHeight(root.left) 
    requires leftWidth == |leftPath| - 1
    requires rightWidth == |rightPath| - 1
    requires root.left != Nil && root.right != Nil
    requires diameter == max(leftWidth, max(rightWidth, TreeHeight(root.left)+TreeHeight(root.right)+2))
    requires |greatestPath|-1 == diameter
    requires isTreePath(greatestPath, start,end)
    requires isValidPath(greatestPath, root)
    requires distinct(greatestPath)
    ensures largestPath(greatestPath, root)
{
    pathSums(root);
    forall start: Tree, end: Tree, paths: seq<Tree> | distinct(paths) && isTreePath(paths, start, end) && isValidPath(paths, root)
        ensures |greatestPath| >= |paths|
    {
        if diameter == leftWidth {
            // assert leftWidth >= rightWidth;
            // assert leftWidth >= TreeHeight(root.left)+TreeHeight(root.right)+2;
            // assert |leftPath| == |greatestPath|;
            // assert |leftPath| >= |rightPath|;
            // rootPathMax(root, rootPath[0], rootPath[|rootPath|-1], rootPath, h);
            // assert |leftPath| >= |rootPath|;
            if root in paths {

            }else{
                pathsWithoutRoot(root, start, end, paths, h);
            }
            assert |greatestPath| >= |paths|;
        } else if diameter == rightWidth {
            // assert |rightPath| == |greatestPath|;
            // assert |rightPath| >= |leftPath|;
            // rootPathMax(root, rootPath[0], rootPath[|rootPath|-1], rootPath, h);
            // assert |rightPath| >= |rootPath|;
            if root in paths {

            }else{
                pathsWithoutRoot(root, start, end, paths, h);
            }
            assert |greatestPath| >= |paths|;

        } else if diameter == TreeHeight(root.left)+TreeHeight(root.right)+2 {
            if root in paths {

            }else{
                pathsWithoutRoot(root, start, end, paths, h);
            }
            assert |greatestPath| >= |paths|;
        }
        //if root in path then pathOptions
        //if root !in path ==> path in rootRight or path in rootLeft
    }
}

lemma LargestRootLeft(root: Tree, h: int, 
leftPath: seq<Tree>, rightPath: seq<Tree>, 
leftWidth: int, rightWidth: int, 
diameter: int, rootPath: seq<Tree>, rootDim: int, greatestPath: seq<Tree>, start: Tree, end: Tree)
    requires ChildrenAreSeparate(root)
    requires root != Nil
    requires h == TreeHeight(root)
    requires largestPath(leftPath, root.left)
    requires largestPath(rightPath, root.right)
    requires largestRootedPath(rootPath, root)

    requires distinct(rootPath)
    requires root in rootPath
    requires rootDim == |rootPath|-1
    requires |rootPath| == 1+TreeHeight(root) 
    requires leftWidth == |leftPath| - 1
    requires rightWidth == |rightPath| - 1
    requires root.left != Nil && root.right == Nil
    requires diameter == max(leftWidth, max(rightWidth, TreeHeight(root.left)+TreeHeight(root.right)+2))
    requires |greatestPath|-1 == diameter
    requires isTreePath(greatestPath, start,end)
    requires isValidPath(greatestPath, root)
    requires distinct(greatestPath)
    ensures largestPath(greatestPath, root)
{
    pathSums(root);
    forall start: Tree, end: Tree, paths: seq<Tree> | distinct(paths) && isTreePath(paths, start, end) && isValidPath(paths, root)
        ensures |greatestPath| >= |paths|
    {
        if diameter == leftWidth {
            if root in paths {

            }else{
                pathsWithoutRoot(root, start, end, paths, h);
            }
            assert |greatestPath| >= |paths|;
        } else if diameter == rightWidth {
            if root in paths {

            }else{
                pathsWithoutRoot(root, start, end, paths, h);
            }
            assert |greatestPath| >= |paths|;

        } else if diameter == TreeHeight(root.left)+TreeHeight(root.right)+2 {
            if root in paths {

            }else{
                pathsWithoutRoot(root, start, end, paths, h);
            }
            assert |greatestPath| >= |paths|;
        }
    }
}

lemma LargestRootRight(root: Tree, h: int, 
leftPath: seq<Tree>, rightPath: seq<Tree>, 
leftWidth: int, rightWidth: int, 
diameter: int, rootPath: seq<Tree>, rootDim: int, greatestPath: seq<Tree>, start: Tree, end: Tree)
    requires ChildrenAreSeparate(root)
    requires root != Nil
    requires h == TreeHeight(root)
    requires largestPath(leftPath, root.left)
    requires largestPath(rightPath, root.right)
    requires largestRootedPath(rootPath, root)

    requires distinct(rootPath)
    requires root in rootPath
    requires rootDim == |rootPath|-1
    requires |rootPath| == 1+TreeHeight(root) 
    requires leftWidth == |leftPath| - 1
    requires rightWidth == |rightPath| - 1
    requires root.left == Nil && root.right != Nil
    requires diameter == max(leftWidth, max(rightWidth, TreeHeight(root.left)+TreeHeight(root.right)+2))
    requires |greatestPath|-1 == diameter
    requires isTreePath(greatestPath, start,end)
    requires isValidPath(greatestPath, root)
    requires distinct(greatestPath)
    ensures largestPath(greatestPath, root)
{
    pathSums(root);
    forall start: Tree, end: Tree, paths: seq<Tree> | distinct(paths) && isTreePath(paths, start, end) && isValidPath(paths, root)
        ensures |greatestPath| >= |paths|
    {
        if diameter == leftWidth {
            if root in paths {

            }else{
                pathsWithoutRoot(root, start, end, paths, h);
            }
            assert |greatestPath| >= |paths|;
        } else if diameter == rightWidth {
            if root in paths {

            }else{
                pathsWithoutRoot(root, start, end, paths, h);
            }
            assert |greatestPath| >= |paths|;

        } else if diameter == TreeHeight(root.left)+TreeHeight(root.right)+2 {
            if root in paths {

            }else{
                pathsWithoutRoot(root, start, end, paths, h);
            }
            assert |greatestPath| >= |paths|;
        }
    }
}


method diameter(root: Tree) returns (heightDim: (int, int))
    requires ChildrenAreSeparate(root)
    ensures root == Nil ==> heightDim == (-1, -1)
    ensures root != Nil && root.left == Nil && root.right == Nil ==> heightDim == (0, 0)
    ensures heightDim.0 == TreeHeight(root)
    ensures root != Nil ==> exists start: Tree, end: Tree, path: seq<Tree> :: isTreePath(path, start, end) && |path| - 1 == heightDim.1  && isValidPath(path, root) && distinct(path) && largestPath(path, root)
{
    if root == Nil {
        return (-1, -1);
    }
    if root.left == Nil && root.right == Nil {
        ghost var path := [root];
        assert isTreePath([root], root, root);
        lpR(root);
        return (0,0);
    }
    var leftDiameter := diameter(root.left);
    var rightDiameter := diameter(root.right);
    var height := max(leftDiameter.0, rightDiameter.0) + 1;
    var dim := leftDiameter.0 + rightDiameter.0 + 2;
    var maxDiameter := max(leftDiameter.1, max(rightDiameter.1, dim));

    if root.right != Nil && root.left != Nil {
        BothCases(root, root.left, root.right, leftDiameter.0, rightDiameter.0);
        ghost var rstart: Tree, rend: Tree, rightPath: seq<Tree> :| isTreePath(rightPath, rstart, rend) && |rightPath| - 1 == rightDiameter.1 && isValidPath(rightPath, root) && distinct(rightPath) && largestPath(rightPath, root.right);
        ghost var lstart: Tree, lend: Tree, leftPath: seq<Tree> :| isTreePath(leftPath, lstart, lend) && |leftPath| - 1 == leftDiameter.1 && isValidPath(leftPath, root) && distinct(leftPath) && largestPath(leftPath, root.left);
        ghost var start, end, path :| root in path && isTreePath(path, start, end) && |path| == leftDiameter.0 + rightDiameter.0 + 3 && isValidPath(path, root) && distinct(path);
        rootPathMax(root, start, end, path, TreeHeight(root));
        if leftDiameter.1 > max(rightDiameter.1, dim) {
            assert maxDiameter == leftDiameter.1;
            // assert largestPath(leftPath, root.right);
            LargestRootBoth(root, TreeHeight(root), leftPath, rightPath, leftDiameter.1, rightDiameter.1, maxDiameter, path, dim, leftPath, lstart, lend);
        }else if rightDiameter.1 > dim {
            LargestRootBoth(root, TreeHeight(root), leftPath, rightPath, leftDiameter.1, rightDiameter.1, maxDiameter, path, dim, rightPath, rstart, rend);
            assert maxDiameter == rightDiameter.1;
        }else{
            assert |path| >= |rightPath|;
            assert |path| >= |leftPath|;
            assert dim >= rightDiameter.1;
            assert dim >= leftDiameter.1;
            assert |path| - 1 == dim;
            assert maxDiameter == dim;
            LargestRootBoth(root, TreeHeight(root), leftPath, rightPath, leftDiameter.1, rightDiameter.1, maxDiameter, path, dim, path, start, end);
        }
    } else if root.right != Nil {
        ghost var rstart: Tree, rend: Tree, rightPath: seq<Tree> :| isTreePath(rightPath, rstart, rend) && |rightPath| - 1 == rightDiameter.1 && isValidPath(rightPath, root) && distinct(rightPath) && largestPath(rightPath, root.right);
        TreeHeightToDescTreePath(root.right, rightDiameter.0);
        ghost var rpath: seq<Tree>, end: Tree :| (end != Nil && end.left == Nil && end.right == Nil && end in TreeSet(root.right))  && isDescTreePath(rpath, root.right, end) && |rpath| == rightDiameter.0+1 && isValidPath(rpath, root.right) && distinct(rpath);
        assert isDescTreePath([root]+rpath, root, end);
        DescTreePathToPath([root]+rpath, root, end);
        assert |[root]+rpath| == rightDiameter.0+2;
        parentNotInTreeSet(root, root.right);
        assert distinct([root]+rpath);
        assert leftDiameter.0 == -1;
        assert leftDiameter.1 == -1;
        NullLargest([], root.left);
        rootPathMax(root, root, end, [root]+rpath, TreeHeight(root));
        if leftDiameter.1 > max(rightDiameter.1, dim) {
            assert false;
        }else if rightDiameter.1 > dim {
            assert maxDiameter == rightDiameter.1;
            assert TreeHeight(root.right)+1 == TreeHeight(root);
            assert |rpath| == TreeHeight(root.right)+1;
            assert |[root]+rpath| == TreeHeight(root.right)+2;
         
            LargestRootRight(root, TreeHeight(root), [], rightPath, leftDiameter.1, rightDiameter.1, maxDiameter, [root]+rpath, dim, rightPath, rstart, rend);
        }else{
            assert dim >= rightDiameter.1;
            assert dim >= leftDiameter.1;
            calc {
                dim;
                leftDiameter.0 + rightDiameter.0 + 2;
                -1 + rightDiameter.0 + 2;
                rightDiameter.0 + 1;
            }
            assert maxDiameter == dim;
            assert |[root]+rpath| - 1 == dim;
            rootPathMax(root, root, end, [root]+rpath, TreeHeight(root));
            LargestRootRight(root, TreeHeight(root), [], rightPath, leftDiameter.1, rightDiameter.1, maxDiameter, [root]+rpath, dim, [root]+rpath, root, end);
        }
    } else if root.left != Nil {
        ghost var lstart: Tree, lend: Tree, leftPath: seq<Tree> :| isTreePath(leftPath, lstart, lend) && |leftPath| - 1 == leftDiameter.1 && isValidPath(leftPath, root.left) && distinct(leftPath) && largestPath(leftPath, root.left);
        TreeHeightToDescTreePath(root.left, leftDiameter.0);
        ghost var lpath: seq<Tree>, end: Tree :| (end != Nil && end.left == Nil && end.right == Nil && end in TreeSet(root.left))  && isDescTreePath(lpath, root.left, end) && |lpath| == leftDiameter.0+1 && isValidPath(lpath, root.left) && distinct(lpath);
        assert isDescTreePath([root]+lpath, root, end);
        DescTreePathToPath([root]+lpath, root, end);
        parentNotInTreeSet(root, root.left);
        assert distinct([root]+lpath);
        assert dim == leftDiameter.0 + 1;
        assert rightDiameter.0 == -1;
        assert rightDiameter.1 == -1;
        assert leftDiameter.1 >= 0;
        NullLargest([], root.right);
        rootPathMax(root, root, end, [root]+lpath, TreeHeight(root));
        if leftDiameter.1 > max(rightDiameter.1, dim) {
            assert maxDiameter == leftDiameter.1;
            LargestRootLeft(root, TreeHeight(root), leftPath, [], leftDiameter.1, rightDiameter.1, maxDiameter, [root]+lpath, dim, leftPath, lstart, lend);
            // Largest(root, TreeHeight(root), leftPath, [], leftDiameter.1, rightDiameter.1, maxDiameter, leftPath, lstart, lend);
        }else if rightDiameter.1 > dim {
            assert false;
        }else{
            assert dim >= rightDiameter.1;
            assert dim >= leftDiameter.1;
            assert maxDiameter == dim;
            LargestRootLeft(root, TreeHeight(root), leftPath, [], leftDiameter.1, rightDiameter.1, maxDiameter, [root]+lpath, dim, [root]+lpath, root, end);
            // Largest(root, TreeHeight(root), leftPath, [], leftDiameter.1, rightDiameter.1, maxDiameter, [root]+lpath, root, end);
        }

    }

    return (height, maxDiameter);
}

method diameterOfBinaryTree(root: Tree) returns (maxDiameter: int)
    requires ChildrenAreSeparate(root)
    ensures root != Nil ==> exists start: Tree, end: Tree, path: seq<Tree> :: isTreePath(path, start, end) && |path| - 1 == maxDiameter && isValidPath(path, root) && distinct(path)
{
    var result := diameter(root);
    maxDiameter := result.1;
}
}