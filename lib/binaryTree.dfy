include "./seq.dfy"

module BinaryTree {
    import opened SeqCustom

    //Definitions
    datatype Tree = Node(val: int, left: Tree, right: Tree) | Nil

    function TreePreorderTraversal(root: Tree): seq<Tree>
        // ensures forall x :: x in TreePreorderTraversal(root) ==> x != Nil
        // ensures forall x :: x in TreePreorderTraversal(root) ==> x != Nil && (x == root || x in TreePreorderTraversal(root.left) || x in TreePreorderTraversal(root.right))
        // ensures forall x :: x in root.repr ==> x in PreorderTraversal(root)
        // ensures injectiveSeq(TreePreorderTraversal(root))
        // ensures forall k :: 0 <= k < |TreePreorderTraversal(root)| ==> TreePreorderTraversal(root)[k] in root.repr
        // ensures forall k :: 0 <= k < |PreorderTraversal(root)| ==> forall child :: child in PreorderTraversal(root)[k].repr && child != child in PreorderTraversal(root)[k] ==> exists j :: k < j < |PreorderTraversal(root)| && PreorderTraversal(root)[j] == child
    {
    if root == Nil then [] else if root.left != Nil && root.right != Nil then [root]+TreePreorderTraversal(root.left)+TreePreorderTraversal(root.right) else if root.left != Nil then [root]+TreePreorderTraversal(root.left) else if root.right != Nil then [root]+TreePreorderTraversal(root.right) else [root]
    }

    predicate validTree(root: Tree) {
        if root != Nil then root.left != root && root.right != root && (forall lchild :: lchild in TreePreorderTraversal(root.left) ==> lchild != root && lchild !in TreePreorderTraversal(root.right)) && (forall rchild :: rchild in TreePreorderTraversal(root.right) ==> rchild != root && rchild !in TreePreorderTraversal(root.left)) && validTree(root.right) && validTree(root.left) else true
        // if root != Nil then root.left != root && root.right != root && root !in TreePreorderTraversal(root.left)  && root !in TreePreorderTraversal(root.right) && forall x :: x in TreePreorderTraversal(root.left) ==> x !in TreePreorderTraversal(root.right) && forall x :: x in TreePreorderTraversal(root.right) ==> x !in TreePreorderTraversal(root.left) && validTree(root.right) && validTree(root.left) else true
    }

    function max(left: int, right: int): int {
        if left > right then left else right
    }

    function TreeSet(root: Tree): set<Tree> {
        match root {
            case Nil => {}
            case Node(val, left, right) => {root}+TreeSet(left)+TreeSet(right)
        }
    }

    function TreeHeight(root: Tree): int 
        ensures TreeHeight(root) >= -1
    {
        if root == Nil then -1 else if root.left == Nil && root.right == Nil then 0 else max(TreeHeight(root.left), TreeHeight(root.right)) + 1
    }

    predicate isChild(a: Tree, b: Tree) {
        a != Nil && (a.left == b || a.right == b)
    }

    predicate isParentOrChild(a: Tree, b: Tree) {
        //a != Nil && b != Nil && (a.left == b || a.right == b || (a == b.left || a == b.right))
        a != Nil && b != Nil && (isChild(a, b) || isChild(b, a))
    }

    predicate isTreePath(path: seq<Tree>, start: Tree, end: Tree) {
        if |path| == 0 then false else if |path| == 1 then start != Nil && start == end && path[0] == start else match path[0] {
            case Nil => false
            case Node(val, left, right) => path[0] == start && path[|path|-1] == end && isParentOrChild(path[0], path[1]) && isTreePath(path[1..], path[1], end)
        }
    }

    predicate isTreePathAlt(path: seq<Tree>, start: Tree, end: Tree) {
        if |path| == 0 then false else if |path| == 1 then start != Nil && start == end && path[0] == start else path[0] == start && start != Nil && end == path[|path|-1] == end && forall i :: 0 <= i < |path| - 1 ==> isParentOrChild(path[i], path[i+1])
    }

    predicate isDescTreePath(path: seq<Tree>, start: Tree, end: Tree) {
        if |path| == 0 then false else if |path| == 1 then match path[0] {
                case Nil => false
                case Node(val, left, right) => path[0] == start && end == start
        } else match path[0] {
            case Nil => false
            case Node(val, left, right) => end != Nil && path[|path|-1] == end && path[0] == start && path[1] != Nil && ((left == path[1] && isDescTreePath(path[1..],left, end)) || (right == path[1] && isDescTreePath(path[1..], right, end)))
        }
    }

    predicate isAscTreePath(paths: seq<Tree>, start: Tree, end: Tree) {
        if |paths| == 0 then 
            false 
        else if |paths| == 1 then match paths[0] {
            case Nil => false
            case Node(val, left, right) => start == paths[0] && end == start
        } else match paths[0] {
            case Nil => false
            case Node(val, left, right) => end != Nil && paths[|paths|-1] == end && start == paths[0] && paths[1] != Nil  && ((paths[0] == paths[1].left && isAscTreePath(paths[1..], paths[1], end)) || (paths[0] == paths[1].right && isAscTreePath(paths[1..], paths[1], end)))
        }
    }

    predicate isAscTreePathAlt(path: seq<Tree>, start: Tree, end: Tree) {
        if |path| == 0 then false else if |path| == 1 then start != Nil && start == end && path[0] == start else path[0] == start && start != Nil && end == path[|path|-1] && forall i :: 0 <= i < |path| -1 ==> isChild(path[i+1], path[i])
    }

    lemma AscTreePathAreTheSame(path: seq<Tree>, start: Tree, end: Tree) 
        requires start != Nil && end != Nil
        requires isAscTreePath(path, start, end)
        ensures isAscTreePathAlt(path, start, end)
    {
        AscTreePathNotNil(path, start, end);
    }

    lemma AscTreePathAreTheSameAlt(path: seq<Tree>, start: Tree, end: Tree) 
        requires start != Nil && end != Nil
        requires isAscTreePathAlt(path, start, end)
        ensures isAscTreePath(path, start, end)
    {
        // AscTreePathNotNil(path, start, end);
    }
    

    ghost predicate ChildrenAreSeparate(root: Tree) {
        root == Nil || (root != Nil && (TreeSet(root.left) !! TreeSet(root.right)) && ChildrenAreSeparate(root.left) && ChildrenAreSeparate(root.right))
    }

    predicate isValidPath(path: seq<Tree>, root: Tree) {
        forall node :: node in path ==> node in TreeSet(root)
    }

    ghost predicate isPath(path: seq<Tree>, start: Tree, end: Tree, root: Tree) {
        isTreePath(path,start, end) && isValidPath(path, root) && distinct(path)
    }

    predicate isLeaf(node: Tree ) {
        node != Nil && node.right == Nil && node.left == Nil
    }

    //lemmas

    lemma rootNotInChildren(root: Tree)
        requires root != Nil
        requires validTree(root);
        ensures root != Nil && root.left != Nil ==> root !in TreePreorderTraversal(root.left)
        ensures root != Nil && root.right != Nil ==> root !in TreePreorderTraversal(root.right)
    {
        assert root in TreePreorderTraversal(root);
        tpt(root);
        if root != Nil && root.left != Nil && root.right != Nil {
            calc {
                TreePreorderTraversal(root);
                [root]+TreePreorderTraversal(root.left)+TreePreorderTraversal(root.right);
            }
            assert root !in TreePreorderTraversal(root.left);
        }else{

        }
    }

    lemma {:verify } TPTInjective(root: Tree) 
        requires validTree(root)
        requires root != Nil
        ensures distinct(TreePreorderTraversal(root))
    {
        NoNil(root);
        tpt(root);
        assert root !in TreePreorderTraversal(root.left);
        assert root !in TreePreorderTraversal(root.right);
        if root.right != Nil && root.left != Nil {
            calc{
                TreePreorderTraversal(root);
                [root]+TreePreorderTraversal(root.left)+TreePreorderTraversal(root.right);
            }
            TPTInjective(root.left);
            TPTInjective(root.right);
            distincts([root], TreePreorderTraversal(root.left));
            distincts([root] + TreePreorderTraversal(root.left), TreePreorderTraversal(root.right));

        }else if root.right != Nil {
            calc{
                TreePreorderTraversal(root);
                [root]+TreePreorderTraversal(root.right);
            }
            TPTInjective(root.right);
            distincts([root], TreePreorderTraversal(root.right));
        }else if root.left != Nil {

            calc{
                TreePreorderTraversal(root);
                [root]+TreePreorderTraversal(root.left);
            }
            TPTInjective(root.left);
            distincts([root], TreePreorderTraversal(root.left));
        }
    }

    lemma NoNil(root: Tree)
        ensures forall x :: x in TreePreorderTraversal(root) ==> x != Nil
    {

    }

    lemma tpt(root: Tree)
        ensures forall x :: x in TreePreorderTraversal(root) ==> x != Nil
        ensures forall x :: x in TreePreorderTraversal(root) ==> x != Nil && (x == root || x in TreePreorderTraversal(root.left) || x in TreePreorderTraversal(root.right))
    {

    }


    lemma AllChildTraversalElementsInRoot(root: Tree, elem: Tree)
        requires elem in TreePreorderTraversal(root)
        ensures forall child :: child in TreePreorderTraversal(elem) ==> child in TreePreorderTraversal(root)
    {

    }

    lemma TreePreorderTraversalSubstrings(root: Tree)
        requires root != Nil
        ensures root.left != Nil ==> isSubstring(TreePreorderTraversal(root.left), TreePreorderTraversal(root))
        ensures root.right != Nil ==> isSubstring(TreePreorderTraversal(root.right), TreePreorderTraversal(root))
    {
    if root.left != Nil && root.right != Nil {
        calc {
            TreePreorderTraversal(root);
            [root]+TreePreorderTraversal(root.left)+TreePreorderTraversal(root.right);
        }
        var k := 1;
        var j := |TreePreorderTraversal(root.left)|+1;
        assert 0 <= k <= j <= |TreePreorderTraversal(root)| && TreePreorderTraversal(root.left) == TreePreorderTraversal(root)[1..|TreePreorderTraversal(root.left)|+1];

        var s := 1+|TreePreorderTraversal(root.left)|;
        var t := |TreePreorderTraversal(root)|;
        assert 0 <= s <= t <= |TreePreorderTraversal(root)| && TreePreorderTraversal(root.right) == TreePreorderTraversal(root)[s..t];
    }else if root.left != Nil && root.right == Nil {
        calc {
            TreePreorderTraversal(root);
            [root]+TreePreorderTraversal(root.left);
        }
        var k := 1;
        var j := |TreePreorderTraversal(root.left)|+1;
        assert 0 <= k <= j <= |TreePreorderTraversal(root)| && TreePreorderTraversal(root.left) == TreePreorderTraversal(root)[1..j];
    }else if root.left == Nil && root.right != Nil {
        calc {
            TreePreorderTraversal(root);
            [root]+TreePreorderTraversal(root.right);
        }
        var k := 1;
        var j := |TreePreorderTraversal(root.right)|+1;
        assert 0 <= k <= j <= |TreePreorderTraversal(root)| && TreePreorderTraversal(root.right) == TreePreorderTraversal(root)[1..j];
    }
    }

    lemma AllContained(root: Tree)
        requires root != Nil
        ensures forall x :: x in TreePreorderTraversal(root) ==> (x == root || x in TreePreorderTraversal(root.left) || x in TreePreorderTraversal(root.right))
    {
    }

    lemma {:induction false} AllChildrenTraversalsAreSubstrings(root: Tree) 
        requires root != Nil
        ensures forall x ::x in TreePreorderTraversal(root) ==> isSubstring(TreePreorderTraversal(x), TreePreorderTraversal(root))
    {
        NoNil(root);
        AllContained(root);
        forall x | x in TreePreorderTraversal(root) 
            ensures isSubstring(TreePreorderTraversal(x), TreePreorderTraversal(root))
        {
            tpt(root);
            if x == root {
                var k, j := 0, |TreePreorderTraversal(root)|;
                assert 0 <= k <= j <= |TreePreorderTraversal(root)| && TreePreorderTraversal(root) == TreePreorderTraversal(root)[k..j];
            }else if x == root.left || x == root.right {
            TreePreorderTraversalSubstrings(root); 
            }else {
                if root.left != Nil && root.right != Nil {
                    assert x != root;
                    assert TreePreorderTraversal(root) == [root] + TreePreorderTraversal(root.left) + TreePreorderTraversal(root.right);
                    if root.left != Nil  && x in TreePreorderTraversal(root.left) {
                        AllChildrenTraversalsAreSubstrings(root.left);
                        assert isSubstring(TreePreorderTraversal(x), TreePreorderTraversal(root.left));
                        TreePreorderTraversalSubstrings(root);
                        AllSubstringsAreSubstrings(TreePreorderTraversal(x), TreePreorderTraversal(root.left), TreePreorderTraversal(root));
                    }
                    if root.right != Nil && x in TreePreorderTraversal(root.right) {
                        AllChildrenTraversalsAreSubstrings(root.right);
                        assert isSubstring(TreePreorderTraversal(x), TreePreorderTraversal(root.right));
                        TreePreorderTraversalSubstrings(root);
                        AllSubstringsAreSubstrings(TreePreorderTraversal(x), TreePreorderTraversal(root.right), TreePreorderTraversal(root));
                    }
                }else if root.left != Nil  && x in TreePreorderTraversal(root.left) {
                    AllChildrenTraversalsAreSubstrings(root.left);
                    assert isSubstring(TreePreorderTraversal(x), TreePreorderTraversal(root.left));
                        TreePreorderTraversalSubstrings(root);
                        AllSubstringsAreSubstrings(TreePreorderTraversal(x), TreePreorderTraversal(root.left), TreePreorderTraversal(root));
                }else  if root.right != Nil && x in TreePreorderTraversal(root.right) {
                    AllChildrenTraversalsAreSubstrings(root.right);
                        assert isSubstring(TreePreorderTraversal(x), TreePreorderTraversal(root.right));
                        TreePreorderTraversalSubstrings(root);
                        AllSubstringsAreSubstrings(TreePreorderTraversal(x), TreePreorderTraversal(root.right), TreePreorderTraversal(root));
                }else{
                    assert x != root;
                    assert x !in TreePreorderTraversal(root.left);
                    assert x !in TreePreorderTraversal(root.right);
                    assert false;
                }
            }
        }
    }

    lemma TreeChildrenAreLater(root: Tree)
        requires root != Nil
        ensures forall x :: x in TreePreorderTraversal(root) && x != root ==> exists k:nat :: 0 < k < |TreePreorderTraversal(root)| && TreePreorderTraversal(root)[k] == x
    {
        NoNil(root);
    }

    lemma TreePreorderTraversalChildrenAreLater3(root: Tree, elem: Tree, k: nat) 
        requires distinct(TreePreorderTraversal(root))
        requires k < |TreePreorderTraversal(root)|
        requires elem in TreePreorderTraversal(root)
        requires elem != Nil
        requires TreePreorderTraversal(root)[k] == elem
        ensures forall child :: child in TreePreorderTraversal(elem) && child != elem ==> exists j: nat :: k < j < |TreePreorderTraversal(root)| && TreePreorderTraversal(root)[j] == child
    {
        // TPTInjective(root);
        AllChildTraversalElementsInRoot(root, elem);
        AllChildrenTraversalsAreSubstrings(root);
        AllChildrenTraversalsAreSubstrings(elem);
        TreeChildrenAreLater(elem);
        forall child | child in TreePreorderTraversal(elem) && child != elem
            ensures exists j: nat :: k < j < |TreePreorderTraversal(root)| && TreePreorderTraversal(root)[j] == child
        {
            assert child in TreePreorderTraversal(root);
            assert child != elem;
            var j:nat :| 0 < j < |TreePreorderTraversal(elem)| && TreePreorderTraversal(elem)[j] == child;
            var s,t :| 0 <= s < t <= |TreePreorderTraversal(root)| && TreePreorderTraversal(elem) == TreePreorderTraversal(root)[s..t];
            assert TreePreorderTraversal(root)[k] == elem;
            assert TreePreorderTraversal(elem)[0] == elem;
            assert TreePreorderTraversal(root)[s] == elem;
            assert s == k;
            assert TreePreorderTraversal(root)[s+j] == child;

            // seqbusiness(TreePreorderTraversal(root), child);
            // var j :| 0 <= j < |TreePreorderTraversal(root)| && TreePreorderTraversal(root)[j] == child;
            // assert isSubstring(TreePreorderTraversal(child), TreePreorderTraversal(elem));
            // AllSubstringsAreSubstrings(TreePreorderTraversal(child), TreePreorderTraversal(elem), TreePreorderTraversal(root));
            // assert isSubstring(TreePreorderTraversal(child), TreePreorderTraversal(root));
            // // assert |TreePreorderTraversal(child)| <= |TreePreorderTraversal(elem)|;
            // var s,t :| 0 <= s < t <= |TreePreorderTraversal(root)| && TreePreorderTraversal(child) == TreePreorderTraversal(root)[s..t];
            // assert j == s;
        }
    }


    lemma TreeHeightMax(root: Tree) 
        ensures forall node :: node in TreeSet(root) ==> TreeHeight(root) >= TreeHeight(node)
    {}

    lemma TreePathsAreTheSameAlt(path: seq<Tree>, start: Tree, end: Tree)
        requires start != Nil
        requires end != Nil
        requires isTreePath(path, start, end)
        ensures isTreePathAlt(path, start, end)
    {

    }
    
    lemma TreePathSplit(path: seq<Tree>, start: Tree, end: Tree) 
        requires start != Nil
        requires end != Nil
        requires |path| > 1
        requires isTreePathAlt(path, start, end)
        ensures forall i :: 1 <= i < |path| ==> isTreePath(path[..i], start, path[i-1])
    {
        TreePathSplitAlt(path, start, end);
        TreePathsAreTheSame(path, start, end);
        TreePathNotNil(path, start, end);
        forall i | 1 <= i < |path| 
            ensures isTreePath(path[..i], start, path[i-1])
        {
            TreePathChildrenAlt(path[..i], start, path[i-1]);
        }
    }

    lemma TreePathSplitAlt(path: seq<Tree>, start: Tree, end: Tree) 
        requires start != Nil
        requires end != Nil
        requires |path| > 1
        requires isTreePathAlt(path, start, end)
        ensures forall i :: 1 <= i < |path| ==> isTreePathAlt(path[..i], start, path[i-1])
    {

    }

    lemma TreePathsCanSplit(path: seq<Tree>, start: Tree, end: Tree, i: nat)
        requires start != Nil
        requires end != Nil
        requires 1 <= i < |path|
        requires |path| > 1
        requires isTreePath(path, start, end)
        ensures isTreePath(path[..i],start, path[i-1])
        ensures isTreePath(path[i..],path[i], end)
    {
        TreePathNotNil(path, start, end);
        TreePathsAreTheSameAlt(path, start, end);
        var left := path[..i];
        var right := path[i..];
        assert path == left + right;
        forall k | 0<= k < |left|-1 
            ensures isParentOrChild(left[k], left[k+1])
        {
            assert k < |left|-1 < |path|;
            assert left[k] in path && left[k+1] in path;
            assert left[k] == path[k];
            assert left[k+1] == path[k+1];
            assert isParentOrChild(path[k], path[k+1]);
        }
        assert isTreePathAlt(left, start, path[i-1]);
        TreePathsAreTheSame(left, start, path[i-1]);

        forall k | 0<= k < |right|-1 
            ensures isParentOrChild(right[k], right[k+1])
        {
        }
        assert isTreePathAlt(right, path[i], end);
    }

    lemma TreePathsAreTheSame(path: seq<Tree>, start: Tree, end: Tree)
        requires start != Nil
        requires end != Nil
        requires isTreePathAlt(path, start, end)
        ensures isTreePath(path, start, end)
    {

    }
    
    lemma TreePathsReverseAreTreePaths(path: seq<Tree>, start: Tree, end: Tree)
        requires start != Nil
        requires end != Nil
        requires isTreePath(path, start, end)
        ensures isTreePath(reverse(path), end, start)
    {
        TreePathsAreTheSameAlt(path, start, end);
        ReverseIndexAll(path);
        forall i | 0 <= i < |path| - 1
            ensures isParentOrChild(reverse(path)[i], reverse(path)[i+1]) 
        {

        }
        TreePathsAreTheSame(reverse(path), end, start);
    }

    lemma DescPathChildren(path: seq<Tree>, start: Tree, end: Tree)
        requires start != Nil
        requires end != Nil
        requires |path| > 1
        requires isDescTreePath(path, start, end)
        ensures forall i :: 0 <= i < |path| - 1 ==> isChild(path[i], path[i+1])
    {
    }

    lemma DescPathChildrenAlt(path: seq<Tree>, start: Tree, end: Tree)
        requires start != Nil
        requires end != Nil
        requires |path| > 0
        requires path[0] == start;
        requires path[|path|-1] == end;
        requires forall i :: 0 <= i < |path| ==> path[i] != Nil
        requires forall i :: 0 <= i < |path| - 1 ==> isChild(path[i], path[i+1])
        ensures isDescTreePath(path, start, end)
    {
    }


    lemma DescTreePathSplitAlt(path: seq<Tree>, start: Tree, end: Tree) 
        requires start != Nil
        requires end != Nil
        requires |path| > 1
        requires isDescTreePath(path, start, end)
        ensures forall i :: 1 <= i < |path| ==> isDescTreePath(path[..i], start, path[i-1])
    {
        DescPathChildren(path, start, end);
        DescTreePathNotNil(path, start, end);
        forall i | 1 <= i < |path|
            ensures isDescTreePath(path[..i], start, path[i-1])
        {
            DescPathChildrenAlt(path[..i], start, path[i-1]);
        }
    }

    lemma DescTreePathSplitAltRev(path: seq<Tree>, start: Tree, end: Tree) 
        requires start != Nil
        requires end != Nil
        requires |path| > 1
        requires isDescTreePath(path, start, end)
        ensures forall i :: 1 <= i < |path| ==> isDescTreePath(path[i..], path[i], end)
    {
        DescPathChildren(path, start, end);
        DescTreePathNotNil(path, start, end);
        forall i | 1 <= i < |path|
            ensures isDescTreePath(path[i..], path[i], end)
        {
            DescPathChildrenAlt(path[i..], path[i], end);
        }
    }

    lemma DescPathChildrenTreeSet(path: seq<Tree>, start: Tree, end: Tree)
        requires start != Nil
        requires end != Nil
        requires |path| > 0
        requires isDescTreePath(path, start, end)
        ensures isValidPath(path, start)
    {
        if |path| == 1 {
            assert path[0] == end;
        }else{
            // assert path == path[..|path|-1]+[end];
            assert path == [start]+path[1..];
            DescPathChildren(path, start, end);
            // DescTreePathSplitAltRev(path, start, end);
        }
    }

    lemma TreePathChildrenAlt(path: seq<Tree>, start: Tree, end: Tree) 
        requires start != Nil
        requires end != Nil
        requires |path| >= 1
        requires path[0] == start;
        requires path[|path|-1] == end;
        requires forall i :: 0 <= i < |path| ==> path[i] != Nil
        requires forall i :: 0 <= i < |path| - 1 ==> isParentOrChild(path[i], path[i+1])
        ensures isTreePath(path, start, end)
    {

    }

    lemma DescPathChildrenReverse(path: seq<Tree>, start: Tree, end: Tree)
        requires start != Nil
        requires end != Nil
        requires |path| > 1
        requires isDescTreePath(path, start, end)
        ensures forall i :: 0 <= i < |reverse(path)| - 1 ==> isChild(reverse(path)[i+1], reverse(path)[i])
    {
        DescPathChildren(path, start, end);
        ReverseIndexAll(path);
    }

    lemma AscPathChildrenAlt(path: seq<Tree>, start: Tree, end: Tree)
        requires start != Nil
        requires end != Nil
        requires |path| > 1
        requires path[0] == start;
        requires path[|path|-1] == end;
        requires forall i :: 0 <= i < |path| - 1 ==> isChild(path[i+1], path[i])
        ensures isAscTreePath(path, start, end)
    {
    }

    lemma AscPathChildren(path: seq<Tree>, start: Tree, end: Tree)
        requires start != Nil
        requires end != Nil
        requires |path| > 1
        requires isAscTreePath(path, start, end)
        ensures forall i :: 0 <= i < |path| - 1 ==> isChild(path[i+1], path[i])
    {
    }

    lemma AscPathChildrenTreeSet(path: seq<Tree>, start: Tree, end: Tree)
        requires start != Nil
        requires end != Nil
        requires |path| > 0
        requires isAscTreePath(path, start, end)
        ensures isValidPath(path, end)
    {
        if |path| == 1 {
            assert path[0] == end;
        }else{
            assert path == path[..|path|-1]+[end];
            AscPathChildren(path, start, end);
            assert start == path[..|path|-1][0];
            AscTreePathSplit(path, start, end);
            assert isAscTreePath(path[..|path|-1], start, path[|path|-2]);
        }
    }
    
    lemma AscTreePathSplitAlt(path: seq<Tree>, start: Tree, end: Tree) 
        requires start != Nil
        requires end != Nil
        requires |path| > 1
        requires isAscTreePathAlt(path, start, end)
        ensures forall i :: 1 <= i < |path| ==> isAscTreePathAlt(path[..i], start, path[i-1])
    {

    }

    lemma AscTreePathSplit(path: seq<Tree>, start: Tree, end: Tree) 
        requires start != Nil
        requires end != Nil
        requires |path| > 1
        requires isAscTreePath(path, start, end)
        ensures forall i :: 1 <= i < |path| ==> isAscTreePath(path[..i], start, path[i-1])
    {
        AscTreePathAreTheSame(path, start, end);
        AscTreePathSplitAlt(path, start, end);
        AscTreePathNotNil(path, start, end);
        forall i | 1 <= i < |path| 
            ensures isAscTreePath(path[..i], start, path[i-1])
        {
            assert path[i-1] in path;
            AscTreePathAreTheSameAlt(path[..i], start, path[i-1]);
        }
    }


    lemma TreeSetChildInTreeSet(root: Tree, child: Tree) 
        requires root != Nil
        requires child != Nil && child in TreeSet(root)
        ensures TreeSet(child) <= TreeSet(root)
    {}

    lemma parentNotInTreeSet(parent: Tree, root: Tree)
        requires parent != Nil && parent != root && (parent.left == root || parent.right == root)
        ensures parent !in TreeSet(root)
    {
        if root == Nil {} else {
            assert TreeSet(root) == {root}+TreeSet(root.left)+TreeSet(root.right);
            parentNotInTreeSet(root, root.left);
            parentNotInTreeSet(root, root.right);
            if parent in TreeSet(root.left) {
                TreeSetChildInTreeSet(root.left, parent);
            }else if parent in TreeSet(root.right) {
                TreeSetChildInTreeSet(root.right, parent);
            }
        }
    }


    lemma childInTreeSet(root: Tree, child: Tree)
        requires root != Nil && child != Nil
        requires isChild(root, child)
        ensures child in TreeSet(root)
    {}

    lemma childrenInTreeSet(root: Tree, child: Tree, path: seq<Tree>)
        requires root != Nil && child != Nil
        requires child in TreeSet(root)
        requires isValidPath(path, child)
        ensures isValidPath(path, root)
    {}

    lemma validChildrenAlt(path: seq<Tree>, start: Tree, end: Tree)
        requires start != Nil
        requires end != Nil
        requires |path| > 1
        requires path[0] == start;
        requires path[|path|-1] == end;
        requires forall i :: 0 <= i < |path| ==> path[i] != Nil
        requires forall i :: 0 <= i < |path| - 1 ==> isChild(path[i], path[i+1])
        requires forall i :: 0 <= i < |path| - 1 ==> path[i+1] in TreeSet(path[i+1])
        ensures forall i :: 0 <= i < |path| - 1 ==> isValidPath(path[i..], path[i])
    {
        if |path| == 2 {
            assert isValidPath(path[0..], path[0]);
            assert isValidPath(path[1..], path[1]);
            assert forall i :: 0 <= i < |path| - 1 ==> isValidPath(path[i..], path[i]);
            assert start in path && end in path;
        }else{
            validChildrenAlt(path[1..], path[1], end);
        }
    }

    lemma isDescPathAndValidImpliesAllValid(path: seq<Tree>, start: Tree, end: Tree) 
        requires isDescTreePath(path, start, end)
        requires isValidPath(path, start)
        requires |path| > 1
        ensures forall i :: 0 <= i < |path| ==> isValidPath(path[i..], path[i]);
    {
        assert path[1] in TreeSet(start);
        assert isDescTreePath(path[1..], path[1], end);
        assert isValidPath(path[1..], start);
        DescTreePathNotNil(path, start, end);
        DescPathChildren(path, start, end);
        assert forall i :: 0 <= i < |path| ==> path[i] in path;
        validChildrenAlt(path, start, end);
    }

    lemma DescPathIsAscPath(path: seq<Tree>, start: Tree, end: Tree)
        requires start != Nil
        requires end != Nil
        requires |path| >= 1
        requires isDescTreePath(path, start, end)
        ensures isAscTreePath(reverse(path), end, start)
    {
        DescTreePathNotNil(path, start, end);
        ReverseIndexAll(path);
        if |path| == 1 {} else {
            DescPathChildrenReverse(path, start, end);
            AscPathChildrenAlt(reverse(path), end, start);
        }
    }

    lemma AscTreePathNotNil(path: seq<Tree>, start: Tree, end: Tree)
        requires start != Nil
        requires end != Nil
        requires |path| >= 1
        requires isAscTreePath(path, start, end)
        ensures forall node :: node in path ==> node != Nil
    {
        if |path| == 1 {
        }else if |path| > 1 {
            assert path == [path[0]]+path[1..];
            AscTreePathNotNil(path[1..], path[1], end);
        }
    }

    lemma AscPathChildrenReverse(path: seq<Tree>, start: Tree, end: Tree)
        requires start != Nil
        requires end != Nil
        requires |path| > 1
        requires isAscTreePath(path, start, end)
        ensures forall i :: 0 <= i < |reverse(path)| - 1 ==> isChild(reverse(path)[i], reverse(path)[i+1])
    {
        AscPathChildren(path, start, end);
        ReverseIndexAll(path);
    }

    lemma AscPathIsDescPath(path: seq<Tree>, start: Tree, end: Tree)
        requires start != Nil
        requires end != Nil
        requires |path| >= 1
        requires isAscTreePath(path, start, end)
        ensures isDescTreePath(reverse(path), end, start)
    {
        AscTreePathNotNil(path, start, end);
        ReverseIndexAll(path);
        // reversePreservesMultiset(path);
        if |path| == 1 {

        }else{
            // assert path[0] == start;
            // assert path[ |path| - 1] == end;
            // assert reverse(path)[0] == end;
            // assert reverse(path)[|path|-1] == start;
            AscPathChildrenReverse(path, start, end);
            // assert forall x :: x in reverse(path) ==> x in path && x != Nil;
            assert forall i :: 0 <= i < |reverse(path)| ==> reverse(path)[i] in path && reverse(path)[i] != Nil;
            DescPathChildrenAlt(reverse(path), end, start);
        }
    }

    lemma DescPathPlusDescPath(path: seq<Tree>, start: Tree, middle: Tree, pathtwo: seq<Tree>, end: Tree)
        requires start != Nil
        requires end != Nil
        requires middle != Nil
        requires isDescTreePath(path, start, middle)
        requires isDescTreePath(pathtwo, middle, end)
        requires |path| > 1
        requires |pathtwo| > 1
        ensures isDescTreePath(path + pathtwo[1..], start, end)
        ensures |path + pathtwo[1..]| == |path|+|pathtwo|-1;
    {
        DescPathChildren(path, start, middle);
        DescPathChildren(pathtwo, middle, end);
        DescTreePathNotNil(path, start, middle);
        DescTreePathNotNil(pathtwo, middle, end);
        assert forall i :: 0 <= i < |path| ==> path[i] in path;
        assert forall i :: 0 <= i < |pathtwo| ==> pathtwo[i] in pathtwo;
        DescPathChildrenAlt(path + pathtwo[1..], start, end);
    }

    lemma DescTreePathNoChildren(path: seq<Tree>, root: Tree, end: Tree)
        requires root != Nil
        requires end != Nil
        requires |path| > 1
        requires isDescTreePath(path, root, end)
        ensures forall x :: x in path[1..] ==> x in TreeSet(root) - {root} 
    {
        if |path| == 2 {
        }else{
            if root.left != Nil && isDescTreePath(path[1..], root.left, end) {
                parentNotInTreeSet(root,root.left);
                forall x | x in path[1..] 
                    ensures x in TreeSet(root) - {root}
                {
                    assert path[1..] == [path[1]]+path[2..];
                }
            }else if root.right != Nil && isDescTreePath(path[1..], root.right, end) {
                parentNotInTreeSet(root,root.right);
                forall x | x in path[1..] 
                    ensures x in TreeSet(root) - {root}
                {
                    assert path[1..] == [path[1]] + path[2..];
                } 
            }
        }
    }

    lemma DescTreePathInjective(path: seq<Tree>, root: Tree, end: Tree)
        requires root != Nil
        requires end != Nil
        requires isDescTreePath(path, root, end)
        ensures distinct(path)
    {
        if |path| == 1 {

        }else{
            assert path[1] == root.left || path[1] == root.right;
            assert root != root.left && root != root.right;
            assert path == [root]+path[1..];
            var rest := path[1..];
            DescTreePathInjective(rest,path[1], end);
            assert distinct(rest);
            DescTreePathNoChildren(path, root, end);
            forall x,y | x != y && 0 <= x <= y < |path| 
                ensures path[x] != path[y]; 
            {
                if x == 0 {
                    assert path[x] == root;
                    assert path[y] in path[1..];
                    assert path[y] != root;
                }else{
                    assert path[x] != path[y];
                }
            }
        }
    }

    lemma DescTreePathToPath(path: seq<Tree>, root: Tree, end: Tree)
        requires root != Nil
        requires end != Nil
        requires isDescTreePath(path, root, end)
        ensures isTreePath(path, root, end)
    {
        assert path[0] == root;
        assert path[|path|-1] == end;
        if |path| == 1 {
            assert path == [root];
            assert isDescTreePath([root], root, end);
            assert root == end;
            assert isTreePath([root], root, end);
        }
    }

    lemma AscTreePathToPath(path: seq<Tree>, root: Tree, end: Tree)
        requires root != Nil
        requires end != Nil
        requires isAscTreePath(path, root, end)
        ensures isTreePath(path, root, end)
    {
        assert path[0] == root;
        assert path[|path|-1] == end;
        if |path| == 1 {
            assert path == [root];
            assert isAscTreePath([root], root, end);
            assert root == end;
            assert isTreePath([root], root, end);
        }
    }

    lemma DescTreePathNotNil(path: seq<Tree>, start: Tree, end: Tree)
        requires start != Nil
        requires end != Nil
        requires |path| >= 1
        requires isDescTreePath(path, start, end)
        ensures forall node :: node in path ==> node != Nil
        ensures forall i :: 0 <= i < |path| ==> path[i] != Nil
    {
        if |path| == 1 {
        }else if |path| > 1 {
            assert path == [path[0]]+path[1..];
            DescTreePathNotNil(path[1..], path[1], end);
        }
    }

    lemma TreePathNotNil(path: seq<Tree>, start: Tree, end: Tree)
        requires start != Nil
        requires |path| >= 1
        requires isTreePath(path, start, end)
        ensures forall node :: node in path ==> node != Nil
        ensures forall i :: 0 <= i < |path| ==> path[i] != Nil
    {
        if |path| == 1 {
        }else if |path| > 1 {
            assert path == [path[0]]+path[1..];
            TreePathNotNil(path[1..], path[1], end);
        }
    }

    lemma TreePlusTree(path: seq<Tree>, start: Tree, root: Tree, pathtwo: seq<Tree>, end: Tree)
        requires start != Nil && root != Nil && end != Nil
        requires start != root && root != end
        requires isTreePath(path, start, root)
        requires isTreePath(pathtwo, root, end)
        ensures isTreePath(path + pathtwo[1..], start, end)
        ensures |path + pathtwo[1..]| == |path|+|pathtwo|-1
    {
        TreePathsAreTheSameAlt(path, start, root);
        TreePathsAreTheSameAlt(pathtwo, root, end);
        assert isTreePathAlt(path + pathtwo[1..], start, end);
        TreePathsAreTheSame(path + pathtwo[1..], start, end);
    }

    lemma DescPlusAsc(path: seq<Tree>, start: Tree, root: Tree, pathtwo: seq<Tree>, end: Tree)
        requires start != Nil && root != Nil && end != Nil
        requires start != root && root != end
        requires isDescTreePath(path, root, end)
        requires isAscTreePath(pathtwo, start, root)
        ensures isTreePath(pathtwo + path[1..], start, end)
    {
        var result := pathtwo + path[1..];
        assert result[0] == start;
        DescTreePathToPath(path, root, end);
        AscTreePathToPath(pathtwo, start, root);
        TreePlusTree(pathtwo, start, root, path, end);
        assert |pathtwo + path[1..]| == |pathtwo| + |path| -1;
    }

    lemma DescPlusDesc(path: seq<Tree>, start: Tree, root: Tree, pathtwo: seq<Tree>, end: Tree)
        requires start != Nil && root != Nil && end != Nil
        requires start != root && root != end
        requires isDescTreePath(path, root, end)
        requires isDescTreePath(pathtwo, root, start)
        ensures isTreePath(reverse(pathtwo) + path[1..], start, end)
    {
        DescPathIsAscPath(pathtwo, root, start);
        assert isAscTreePath(reverse(pathtwo), start, root);
        DescPlusAsc(path, start, root, reverse(pathtwo), end);
    }


    lemma isPathSlices(path: seq<Tree>, start: Tree, end: Tree, root: Tree) 
        requires |path| >= 1
        requires isPath(path, start, end, root)
        ensures forall i :: 0 < i < |path| ==> isPath(path[..(i+1)], start, path[i], root) && isPath(path[i..], path[i], end, root)
    {
        TreePathNotNil(path, start, end);
        TreePathsAreTheSameAlt(path, start, end);
        forall i | 0 < i < |path| 
            ensures isPath(path[..(i+1)], start, path[i], root) && isPath(path[i..], path[i], end, root)
        {
            assert path == path[..i]+path[i..];
            TreePathChildrenAlt(path[..(i+1)], start, path[i]);
            TreePathChildrenAlt(path[i..], path[i], end);
            assert isValidPath(path[..i], root);
            assert isValidPath(path[i..], root);
            assert distinct(path[..i]);
            assert distinct(path[i..]);
        }
    }

    lemma notRootNotDesc(root: Tree, start: Tree, end: Tree, path: seq<Tree>)
        requires isValidPath(path, root)
        requires root in path
        ensures start != root ==> !isDescTreePath(path, start, end)
    {
        if isDescTreePath(path, start, end) {
            descRoot(root, start, end, path);
        }
    }

    lemma TreePathStartingAtRootIsChildSeries(root: Tree, start: Tree, end: Tree, path: seq<Tree>) 
        requires root != Nil && end != Nil
        requires |path| > 1
        requires isPath(path, root, end, root)
        requires root in path && root == start;
        ensures forall i :: 0 <= i < |path| - 1 ==> isChild(path[i], path[i+1])
    {
        TreePathNotNil(path, start, end);
        assert [root] == path[..1];
        TreePathsAreTheSameAlt(path, root, end);
        forall k: nat | k < 1
            ensures isChild(path[k], path[k+1])
        {
            assert isParentOrChild(path[k], path[k+1]);
            if isChild(path[k+1], path[k]) {
                parentNotInTreeSet(path[k+1], root);
            }
        }
        DescPathAccumulatesParents(path,[root], 1, {root}, root, end);
    }

    lemma DescPathAccumulatesParents(path: seq<Tree>, pathSub: seq<Tree>,  i: nat, parentset: set<Tree>, root: Tree, end: Tree)
        requires |path| >= 1
        requires 1 <= i < |path|
        requires isTreePath(path, root, end)
        requires forall k:nat :: k < |path| ==> path[k] != Nil 
        requires forall k: nat :: k < i ==> path[k] in parentset
        requires forall k: nat :: k < i ==> isChild(path[k], path[k+1])
        requires distinct(path)
        requires pathSub == path[..i] && |pathSub| >= 1
        requires isDescTreePath(pathSub, root, path[i-1])
        requires i < |path|-1 ==> isParentOrChild(path[i], path[i+1])
        requires root == path[0];
        ensures i < |path|-1 ==> isChild(path[i], path[i+1])
        ensures forall i :: 0 <= i < |path| - 1 ==> isChild(path[i], path[i+1])
        decreases |path|-i
    {
        if i < |path|-1 {
            TreePathsAreTheSameAlt(path, root, end);
            if isChild(path[i+1], path[i]) {
                assert isChild(path[i-1], path[i]);
                parentsAreTheSame(path[i+1], path[i-1], path[i]);
                assert false;
            }else if isChild(path[i], path[i+1]) {
                if |pathSub| == 1 {

                }else{
                DescPathChildren(pathSub, root, path[i-1]);
                DescPathChildrenAlt(pathSub+[path[i]], root, path[i]);
                }
                assert isDescTreePath(pathSub+[path[i]], root, path[i]);
                DescPathAccumulatesParents(path, pathSub+[path[i]], i+1, parentset+{path[i]}, root, end);
            }
        }
    }

    lemma TreePathStartingAtRootIsDesc(path: seq<Tree>, start: Tree, end: Tree, root: Tree) 
        requires root != Nil && end != Nil
        requires isPath(path, start, end, root)
        requires root in path && root == start;
        ensures isDescTreePath(path, start, end)
    {
        if |path| == 1 {
        }else{
            TreePathNotNil(path, start, end);
            TreePathsAreTheSameAlt(path, start, end);
            TreePathSplit(path, start, end);
            TreePathStartingAtRootIsChildSeries(root, start, end, path);
            DescPathChildrenAlt(path, start, end);
        }
    }

    lemma descRoot(root: Tree, start: Tree, end: Tree, path: seq<Tree>) 
        requires isDescTreePath(path, start, end)
        requires isValidPath(path, root)
        requires root in path
        ensures start == root
    {
        if start == root {

        }else {
            assert path[0] != root;
            assert path == [path[0]]+path[1..];
            assert root in path[1..];
            DescPathChildren(path, start, end);
            var i :| 0 < i< |path| && path[i] == root;
            assert isChild(path[i-1], root);
            parentNotInTreeSet(path[i-1], root);
            assert false;
        }
    }

    lemma LastNotRootNotAsc(root: Tree, start: Tree, end: Tree, path: seq<Tree>)
        requires isValidPath(path, root)
        requires root in path
        ensures end != root ==> !isAscTreePath(path, start, end)
    {
        if isAscTreePath(path, start, end) {
            ascRoot(root, start, end, path);
        }
    }

    lemma ascRoot(root: Tree, start: Tree, end: Tree, path: seq<Tree>)
        requires isAscTreePath(path, start, end)
        requires isValidPath(path, root)
        requires root in path
        ensures end == root
    {
        if end == root {

        }else {
            assert path[|path|-1] != root;
            AscPathChildren(path,start,end);
            var i :| 0 <= i < |path|-1 && path[i] == root;
            assert isChild(path[i+1], path[i]);
            parentNotInTreeSet(path[i+1], root);
            assert false;
        }
    }

    lemma TreeHeightToDescTreePath(root: Tree, h: int) 
        requires root != Nil
        requires h == TreeHeight(root)
        ensures exists end: Tree, path: seq<Tree> :: (isLeaf(end) && end in TreeSet(root))  && isDescTreePath(path, root, end) && |path| == h+1 && isValidPath(path, root) && distinct(path)
    {
        if h == 0 {
            assert isDescTreePath([root], root, root);
            assert isValidPath([root], root);
            assert distinct([root]);
            assert root in TreeSet(root);
        }else if h >= 1 {
            if root.left != Nil && TreeHeight(root.left) == h-1 {
                TreeHeightToDescTreePath(root.left, h-1);
                TreeSetChildInTreeSet(root, root.left);
                var end: Tree, path: seq<Tree> :| isLeaf(end) && end in TreeSet(root.left) && isDescTreePath(path, root.left, end) && |path| == h && isValidPath(path, root.left) && distinct(path);
                assert end != Nil && isDescTreePath([root]+path, root, end) && |[root]+path| == h+1;
                parentNotInTreeSet(root, root.left);
                distincts([root], path);
                assert distinct([root]+path);
                assert isValidPath([root]+path, root);
            } else if root.right != Nil && TreeHeight(root.right) == h-1 {
                TreeHeightToDescTreePath(root.right, h-1);
                TreeSetChildInTreeSet(root, root.right);
                var end: Tree, path: seq<Tree> :| isLeaf(end) && end in TreeSet(root.right) && isDescTreePath(path, root.right, end) && |path| == h && isValidPath(path, root.right) && distinct(path);
                assert end != Nil && isDescTreePath([root]+path, root, end) && |[root]+path| == h+1;
                parentNotInTreeSet(root, root.right);
                distincts([root], path);
                assert distinct([root]+path);
                assert isValidPath([root]+path, root);
            }else {
                assert false;
            }
        }
    }

    lemma parentsAreTheSame(p1: Tree, p2: Tree, child: Tree)
        requires p1 != Nil && p2 != Nil && child != Nil
        requires isChild(p1, child)
        requires isChild(p2, child)
        ensures p1 == p2

    lemma pathStartingAtRootDescSlice(root: Tree, start: Tree, end: Tree, path: seq<Tree>, i: int)
        requires root != Nil
        requires root in path && path[0] == root
        requires ChildrenAreSeparate(root)
        requires isPath(path, start, end, root)
        requires 0 < i <= |path|
        requires isDescTreePath(path[0..i], root, path[i-1])
        requires |path| >= 1
        decreases |path| - i
        ensures isDescTreePath(path, root, end)
    {
        TreePathNotNil(path, start, end);
        TreePathsAreTheSameAlt(path, start,end);
        if i < |path| {
            if isChild(path[i-1], path[i]) {
                if i == 1 {
                    assert isDescTreePath(path[0..1], root, path[i-1]);
                }else{

                    DescPathChildren(path[0..i], root, path[i-1]);
                }
                DescPathChildrenAlt(path[0..(i+1)], root, path[i]);
                assert isDescTreePath(path[0..(i+1)], root, path[i]);
                pathStartingAtRootDescSlice(root, start, end, path, i+1);
            }else if isChild(path[i], path[i-1]) {
                if i == 1 {
                    parentNotInTreeSet(path[i],root);
                }else{
                    DescPathChildren(path[0..i], root, path[i-1]);
                    assert isChild(path[i-2],path[i-1]);
                    parentsAreTheSame(path[i-2], path[i], path[i-1]);
                    assert path[i-2] == path[i];
                    assert false;
                }
                assert false;
            }else{
                assert !isParentOrChild(path[i-1], path[i]);
                assert false;
            }
        }else{
            assert i == |path|;
            assert isDescTreePath(path[0..|path|], root, path[|path|-1]);
            assert path[0..|path|] == path;
        }
    }

    lemma pathStartingAtRootDesc(root: Tree, start: Tree, end: Tree, path: seq<Tree>)
        requires root != Nil
        requires root in path && path[0] == root
        requires ChildrenAreSeparate(root)
        requires isPath(path, start, end, root)
        requires |path| >= 1
        decreases |path|
        ensures isDescTreePath(path, root, end)
    {
        if |path| == 1 {

        }else{
            if isChild(path[1], root) {
                parentNotInTreeSet(path[1], root);
                assert false;
            }else if isChild(root, path[1]) {
                assert path[1] == root.left || path[1] == root.right;
                assert isDescTreePath([root, path[1]], root, path[1]);
                pathStartingAtRootDescSlice(root, start, end, path, 1);
            }
        }
    }

    lemma EndDeterminesPath(path: seq<Tree>, start: Tree, end: Tree)
        requires |path| > 1
        requires start != Nil && end != Nil
        requires isDescTreePath(path, start, end)
        requires isValidPath(path, start);
        requires ChildrenAreSeparate(start)
        ensures end in TreeSet(start.left) ==> path[1] == start.left
        ensures end in TreeSet(start.right) ==> path[1] == start.right
    {
        isDescPathAndValidImpliesAllValid(path, start, end);
    }

    lemma ChildHeightBound(root: Tree, h: int) 
        requires root != Nil && root.right != Nil
        requires TreeHeight(root) == h
        ensures TreeHeight(root.right) <= h-1
        ensures TreeHeight(root.left) <= h-1
    {

    }

    lemma RootBounded(root: Tree, h: int) 
        requires root != Nil
        requires TreeHeight(root) == h
        ensures (TreeHeight(root.right) == h-1 && TreeHeight(root.left) <= h-1) || (TreeHeight(root.right) <= h-1 && TreeHeight(root.left) == h-1)
    {

    }
}