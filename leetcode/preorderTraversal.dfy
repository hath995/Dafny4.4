include "./invertTree.dfy"

module PreorderTraversal {
    import opened InvertBinaryTree
    method SetToSeq<T>(s: set<T>) returns (xs: seq<T>)
      ensures multiset(s) == multiset(xs)
    {
      xs := [];
      var left: set<T> := s;
      while left != {}
        invariant multiset(left) + multiset(xs) == multiset(s)
      {
        var x :| x in left;
        left := left - {x};
        xs := xs + [x];
      }
    }

    function children(node: TreeNode): set<TreeNode> 
        reads node, node.repr
    {
        (if node.right != null then {node.right} else {}) + 
        (if node.left != null then {node.left} else {})
    }
    function childStack(node: TreeNode?): seq<TreeNode> 
        reads node
    {
        if node == null then [] else
        (if node.right != null then [node.right] else []) + 
        (if node.left != null then [node.left] else [])
    }

    function mapNodes(ss: seq<TreeNode>): seq<int> 
        reads set i | 0 <= i < |ss| :: ss[i]
    {
        if ss == [] then [] else [ss[0].val]+mapNodes(ss[1..])
    }    

  predicate compare(a: TreeNode, b: TreeNode)
    reads a, b
  {
    a.val <= b.val
  }

lemma ThereIsAMinimum(s: set<TreeNode>)
  requires s != {}
  ensures exists x :: x in s && forall y :: y in s ==> compare(x, y)
{
  var x :| x in s;
  if s == {x} {
    // obviously, x is the minimum
  } else {
    // The minimum in s might be x, or it might be the minimum
    // in s - {x}. If we knew the minimum of the latter, then
    // we could compare the two.
    // Let's start by giving a name to the smaller set:
    var s' := s - {x};
    // So, s is the union of s' and {x}:
    assert s == s' + {x};
    // The following lemma call establishes that there is a
    // minimum in s'.
    ThereIsAMinimum(s');
  }
}

// lemma ThereIsAMinimumTwo(s: set<int>)
//   requires s != {}
//   ensures exists x :: x in s && forall y :: y in s ==> x <= y
// {
//   var x :| x in s;
//   if s == {x} {
//   } else {
//     var s' := s - {x};
//     assert s == s' + {x};
//     ThereIsAMinimumTwo(s');
//   }
// }

//     ghost function gmapNodeSet(ss: set<TreeNode>): set<int> 
//         reads ss
//         ensures forall xx :: xx in gmapNodeSet(ss) ==> exists s :: s in ss && s.val == xx
//     {
//         if ss == {} then 
//             {}
//         else 
//             var s :| s in ss;
//             {s.val}+gmapNodeSet(ss - {s})
//     }    

// lemma ThereIsAMinimumG(s: set<TreeNode>)
//   requires s != {}
//   ensures exists x :: x in gmapNodeSet(s) && forall y :: y in gmapNodeSet(s) ==> x<= y
// {
//     var xx :| xx in s  && gmapNodeSet(s) == {xx.val}+gmapNodeSet(s-{xx});
//     var x :| x in gmapNodeSet(s) && xx.val == x;
//   if s == {xx} {
//     // obviously, x is the minimum
//   } else {
//     var s' := s - {xx};
//     assert s == s' + {xx};
//     ThereIsAMinimumG(s');
//     var mm :| mm in gmapNodeSet(s') && forall y :: y in gmapNodeSet(s') ==> mm <= y;
//     if x <= mm {
//       assert x in gmapNodeSet(s) && forall y :: y in gmapNodeSet(s) ==> x <= y;
//     }else{
//       assert mm in gmapNodeSet(s) && forall y :: y in gmapNodeSet(s) ==> mm <= y;
        
//     }
//   }
// }

    predicate uniqueNodes(ss: set<TreeNode>)
      reads ss
    {
      forall x,y :: x in ss && y in ss && x != y ==> x.val != y.val 
    }


    // function mapNodeSet(ss: set<TreeNode>): set<int> 
    //   reads ss
    //   requires uniqueNodes(ss)
    // {
    //     if ss == {} then 
    //         {}
    //     else 
    //       ThereIsAMinimum(ss);
    //       // ThereIsAMinimumG(ss);
    //       var s :| s in ss && forall ys :: ys in ss ==> compare(s, ys);
    //       {s.val}+mapNodeSet(ss - {s})
    // }    
    
    method Traverse(root: TreeNode) returns (result: seq<TreeNode>)
        requires root.Valid()
        decreases *
    {
        var stack := [root];
        var i := 0;
        result := [];
        var visited: set<TreeNode> := {};
        var visiteds: seq<TreeNode> := [];
        var unvisited: set<TreeNode> := root.repr;
        var parents: seq<TreeNode> := [];
        var parentIndices: seq<int> := [];
        while |stack| > 0 
            invariant |parents| == |parentIndices|
            decreases *
        {
            print "i: ", i, "\n";
            print "pre ", "result ", mapNodes(result), " \n";
            print "pre ", "stack ", mapNodes(stack), " \n";
            print "pre ", "parents ", mapNodes(parents), " \n";
            print "pre ", "parentIndices ", parentIndices, " \n";
            print "pre ", "visited ", mapNodes(visiteds), " \n";
            var current := stack[|stack|-1];
            var stack' := childStack(current);
            if |stack'| > 0 {
                parentIndices := parentIndices + [i];
                parents := parents + [current];
            }
            stack := stack[..|stack|-1]+stack';
            result := result + [current];
            visited := visited + {current};
            visiteds := visiteds + [current];
            unvisited := unvisited-{current};
            if |parents| > 0 { 
              var childnodes := SetToSeq(children(parents[|parents|-1]));
              print "children, ", mapNodes(childnodes);
            }
            if |parents| > 0 && children(parents[|parents|-1]) <= visited {
                parents := parents[..|parents|-1];
                parentIndices := parentIndices[..|parentIndices|-1];
            }

            print "post ", "result ", mapNodes(result), " \n";
            print "post ", "stack ", mapNodes(stack), " \n";
            print "post ", "parents ", mapNodes(parents), " \n";
            print "post ", "parentIndices ", parentIndices, " \n";
            print "post ", "visited ", mapNodes(visiteds), " \n";
            i := i + 1;
        }
        return result;
    }

    method Main() 
      decreases *
    {
        var u := new TreeNode(20, null, null);
        var v := new TreeNode(21, null, null);
        var l := new TreeNode(12, u, v);
        var m := new TreeNode(13, null, null);
        var h := new TreeNode(8, l, m);
        var o := new TreeNode(14, null, null);
        var p := new TreeNode(15, null, null);
        var i := new TreeNode(9, o, p);
        var d := new TreeNode(4, h, i);
        var e := new TreeNode(5, null, null);
        var b := new TreeNode(2, d, e);
        var c := new TreeNode(3, null, null);
        var a := new TreeNode(1, b, c);
        var flat := Traverse(a);
        print mapNodes(flat), "\n";
        print mapNodes(PreorderTraversal(a)), "\n";

    }
}