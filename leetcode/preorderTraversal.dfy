include "./invertTree.dfy"

module PreorderTraversal {
    import opened InvertBinaryTree
    import Std.Collections.Seq
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

    function toSet<T>(s: seq<T>): set<T> 
      decreases |s|
    {
      if s == [] then {} else toSet(s[..|s|-1])+{s[|s|-1]}
    }

    function children(node: TreeNode): set<TreeNode> 
        // requires node.Valid()
        reads node
        // ensures children(node) < node.repr
        // ensures node !in children(node)
    {
        (if node.right != null then {node.right} else {}) + 
        (if node.left != null then {node.left} else {})
    }
    function childStack(node: TreeNode?): seq<TreeNode> 
        reads if node == null then {} else node.repr
        requires node != null ==> node.Valid()
        ensures forall x :: x in childStack(node) ==> x.Valid()
    {
        if node == null then [] else
        (if node.right != null then 
        assert node.Valid();
        assert node.right.Valid();
        [node.right] else []) + 
        (if node.left != null then
        assert node.Valid();
        assert node.left.Valid();
         [node.left] else [])
    }

    function rightStack(node: TreeNode): seq<TreeNode> 
        reads node
        // requires node.Valid()
    {
      if node.right != null then [node.right] else []
    }

    function rightStackVisited(node: TreeNode, visited: set<TreeNode>): seq<TreeNode> 
        reads node
        // requires node.Valid()
    {
      if node.right != null && node.right !in visited then [node.right] else []
    }

    lemma childStackLemma(node: TreeNode?)
        requires node != null ==> node.Valid()
        ensures node == null ==> childStack(node) == []
        ensures node != null && node.left == null && node.right == null ==> childStack(node) == []
        ensures node != null && node.left != null && node.right == null ==> childStack(node) == [node.left]
        ensures node != null && node.left == null && node.right != null ==> childStack(node) == [node.right]
        ensures node != null && node.left != null && node.right != null ==> childStack(node) == [node.right, node.left]
        ensures node != null ==> TreeUnion(childStack(node)) == node.repr-{node}
      {
        if node == null {

        } else{
          if node.right != null && node.left != null {
              assert node.right.repr + node.left.repr == node.repr - {node};
              TreeUnionConcat([node.right],[ node.left]);
              assert TreeUnion(childStack(node)) == node.right.repr + node.left.repr;
            } else if node.right != null && node.left == null {
            } else if node.right == null && node.left != null {
            }else {
            }
        }
      }

    function mapNodes(ss: seq<TreeNode>): seq<int> 
        reads set i | 0 <= i < |ss| :: ss[i]
    {
        if ss == [] then [] else [ss[0].val]+mapNodes(ss[1..])
    }    

    function parentStack(node: TreeNode): seq<TreeNode> 
      reads node, node.repr
      requires node.Valid()
    {
      if |childStack(node)| > 0 then [node] else []
    }

    lemma parentStackLemma(node: TreeNode)
      requires node.Valid()
      ensures forall x :: x in parentStack(node) ==> x.Valid()
    {

    }

    // ghost function AllReprs(ss: seq<TreeNode>): set<TreeNode>
    //   reads ss, ss[0]
    // {
    //   if ss == []  then {} else ss[0].repr + AllReprs(ss[1..])
    // }

    function setUnion<T>(xs: seq<set<T>>): set<T> {
      if xs == [] then {} else xs[0] + setUnion(xs[1..])
    }

    function reprUnion(xs: seq<TreeNode>): set<TreeNode> 
      reads xs
      ensures forall x :: x in xs ==> x.repr <= reprUnion(xs)
    {
      if xs == [] then {} else xs[0].repr + reprUnion(xs[1..])
    }

    function pruneParents(ss: seq<TreeNode>, visited: set<TreeNode>): seq<TreeNode> 
      // reads (set i | 0 <= i < |ss| :: ss[i]) + setUnion(Seq.Map((x: TreeNode) reads x => x.repr, ss))
      reads (set i | 0 <= i < |ss| :: ss[i])
        // reads AllReprs(ss)
        // reads ss
        // requires forall x :: x in ss ==> x.Valid()
        ensures forall x :: x in pruneParents(ss, visited) ==> x in ss
    {
      if ss != [] then if children(ss[|ss|-1]) <= visited then pruneParents(ss[..|ss|-1], visited) else ss else []
    }

    lemma pruneParentsLemma(ss: seq<TreeNode>, visited: set<TreeNode>)
      requires AllAncestors(ss)
      ensures AllAncestors(pruneParents(ss, visited))
    {

    }

  predicate compare(a: TreeNode, b: TreeNode)
    reads a, b
  {
    a.val <= b.val
  }

  predicate AllAncestors(ts: seq<TreeNode>) 
      reads set i | 0 <= i < |ts| :: ts[i]
  {
    forall i :: 0 <= i < |ts|-1 ==> childOf(ts[i+1], ts[i])
  }

  predicate AllAncestorsDesc(ts: seq<TreeNode>) 
      reads set i | 0 <= i < |ts| :: ts[i], reprUnion(ts), set i | 0 <= i < |ts| :: ts[i].left, set i | 0 <= i < |ts| :: ts[i].right
  {
    forall i :: 0 <= i < |ts|-1 ==> childOf(ts[i+1], ts[i]) || descOf(ts[i+1], ts[i])
  }

  predicate childOf(a: TreeNode, b: TreeNode)
    reads a,b
  {
    a == b.left || a == b.right
  }

  predicate descOf(a: TreeNode, b: TreeNode)
    reads a,b,b.repr, if b.left != null then {b.left} else {}, if b.right != null then {b.right} else {}
  {
    (b.left != null && a in b.left.repr) || (b.right != null && a in b.right.repr)
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
            assert current.Valid();
            if current.right != null && current.left != null {
                // assert AllDisjoint(stack[..|stack|-1]+[current.right, current.left]);
            } else if current.right != null && current.left == null {
                assert current.right.repr < current.repr;
                // assert AllDisjoint(stack[..|stack|-1]+[current.right]);
            } else if current.right == null && current.left != null {
                // assert AllDisjoint(stack[..|stack|-1]+[current.left]);
            }else {
                // assert AllDisjoint(stack[..|stack|-1]);
            }
    }

    lemma  TreeUnionMaint(stack: seq<TreeNode>, current: TreeNode, unvisited: set<TreeNode>)
        requires |stack| > 0
        requires unvisited == TreeUnion(stack)
        requires AllDisjoint(stack)
        requires forall x :: x in stack ==> x.Valid()
        requires current == stack[|stack|-1]
        ensures TreeUnion(stack[..|stack|-1]+childStack(current)) == unvisited-{current}
    {
        childStackLemma(current);
        // assert current.Valid();
        assert stack == stack[..|stack|-1]+[stack[|stack|-1]];
        TreeUnionConcat(stack[..|stack|-1],[stack[|stack|-1]]);
        // assert TreeUnion(stack) == TreeUnion(stack[..|stack|-1])+TreeUnion([stack[|stack|-1]]);
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
        // assert TreeUnion(stack[..|stack|-1]) == unvisited-current.repr;
        if current.left != null && current.right != null {
            assert current.right.repr + current.left.repr + {current} == current.repr;
            assert current.right.repr + current.left.repr == current.repr - {current};
            TreeUnionConcat([current.right],[current.left]);
            // assert TreeUnion([current.right, current.left]) == current.right.repr + current.left.repr;
            TreeUnionConcat(stack[..|stack|-1], [current.right, current.left]);
        } else if current.left != null && current.right == null {
            assert current.left.repr == current.repr - {current};
            TreeUnionConcat(stack[..|stack|-1], [current.left]);
            
        }else if current.left == null && current.right != null {
            assert current.right.repr == current.repr - {current};
            TreeUnionConcat(stack[..|stack|-1], [current.right]);

        }else if current.left == null && current.right == null {
            TreeUnionConcat(stack[..|stack|-1], []);

        }
    }

    lemma {:verify false} {:vcs_split_on_every_assert} traverseMaint(
        root: TreeNode,
        result: seq<TreeNode>,
        visited: set<TreeNode>,
        stack: seq<TreeNode>,
        parents: seq<TreeNode>,
        unvisited: set<TreeNode>,
        i: int)
      requires |stack| > 0 
      requires root.Valid()
      requires toSet(result) == visited
      requires forall x :: x in parents ==> x.Valid()
      requires forall x :: x in stack ==> x.Valid()
      requires forall x :: x in stack ==> x in root.repr
      requires forall x :: x in visited ==> x in root.repr
      requires AllAncestors(parents)
      requires stack == [root] ==> parents == []
      requires parents != [] ==> childOf(stack[ |stack| -1], parents[ |parents| -1])
      requires parents != [] ==> stackPred2(stack, parents, visited)
      requires unvisited !! visited
      requires unvisited + visited == root.repr
      // requires visited <= root.repr
      // requires |visited| <= |root.repr|
      requires forall x :: x in stack ==> x in unvisited
      requires AllDisjoint(stack)
      requires unvisited == TreeUnion(stack)
      // requires i == |result|
      // requires i == |visited|
      // requires 0 <= i <= |PreorderTraversal(root)|
      // requires result == PreorderTraversal(root)[..i]
      // requires |stack| > 0 && i < |PreorderTraversal(root)| ==> stack[|stack|-1] == PreorderTraversal(root)[i]
      ensures AllAncestors(pruneParents(parents+parentStack(stack[|stack|-1]), visited+{stack[|stack|-1]}))
      ensures forall x :: x in pruneParents(parents+parentStack(stack[|stack|-1]), visited+{stack[|stack|-1]}) ==> x.Valid()
      // ensures stack[..|stack|-1]+childStack(stack[|stack|-1]) == 
    {
      assert forall x :: x in parents+parentStack(stack[|stack|-1]) ==> x.Valid() by {
        forall x | x in parents+parentStack(stack[|stack|-1])
          ensures x.Valid()
        {
          if x in parents {
            assert x.Valid();
          }else{
          parentStackLemma(stack[|stack|-1]);
            assert x in parentStack(stack[|stack|-1]);
            assert x.Valid();
          }
        }
      }
      assert forall x :: x in pruneParents(parents+parentStack(stack[|stack|-1]), visited+{stack[|stack|-1]}) ==> x.Valid() by {
        forall x | x in pruneParents(parents+parentStack(stack[|stack|-1]), visited+{stack[|stack|-1]})
          ensures x.Valid()
        {
          assert x in parents+parentStack(stack[ |stack|-1]);
          assert x.Valid();
        }
      }
      assert AllAncestors(pruneParents(parents+parentStack(stack[|stack|-1]), visited+{stack[|stack|-1]})) by {
        assert AllAncestors(parents+parentStack(stack[|stack|-1]));
        pruneParentsLemma(parents+parentStack(stack[|stack|-1]), visited+{stack[|stack|-1]});
      }
      var newParents := pruneParents(parents, visited+{stack[|stack|-1]})+parentStack(stack[|stack|-1]);
      var newStack := stack[..|stack|-1]+childStack(stack[|stack|-1]);
      if newParents != [] && parents != [] {
        if |childStack(stack[|stack|-1])| > 0 {
          assert parentStack(stack[|stack|-1]) == [stack[|stack|-1]];
        }else{
          assert parentStack(stack[|stack|-1]) == [];
        }
        // assert childOf(newStack[|newStack|-1], newParents[|newParents|-1]);
        assert stackPred2(newStack, newParents, visited+{stack[|stack|-1]}) by {
          if stack == Seq.Flatten(Seq.Map(rightStack, parents)) {

          }else if stack == Seq.Flatten(Seq.Map(rightStack, parents[..|parents|-1]))+childStack(parents[|parents|-1]) {

          }
        }
      }
    }

    predicate stackPred(stack: seq<TreeNode>, parents: seq<TreeNode>) 
      reads parents, set i | 0 <= i < |parents| :: parents[i], reprUnion(parents)
      requires forall parent :: parent in parents ==> parent.Valid()
    {
      stack == Seq.Flatten(Seq.Map(rightStack, parents)) || (|parents| > 0 && stack == Seq.Flatten(Seq.Map(rightStack, parents[..|parents|-1]))+childStack(parents[|parents|-1]))
    }

    predicate stackPred2(stack: seq<TreeNode>, parents: seq<TreeNode>, visited: set<TreeNode>) 
      reads parents, set i | 0 <= i < |parents| :: parents[i], reprUnion(parents)
      requires forall parent :: parent in parents ==> parent.Valid()
    {
      var visitMap := (x: TreeNode) reads x => rightStackVisited(x, visited);
      stack == Seq.Flatten(Seq.Map(visitMap, parents)) || (|parents| > 0 && stack == Seq.Flatten(Seq.Map(visitMap, parents[..|parents|-1]))+childStack(parents[|parents|-1]))
    }
    
    method {:verify false} {:vcs_split_on_every_assert} Traverse(root: TreeNode) returns (result: seq<TreeNode>)
        requires root.Valid()
        ensures result == PreorderTraversal(root)
    {
        var stack := [root];
        var pro := PreorderTraversal(root);
        assert |pro| == root.TreeSize();
        var i := 0;
        result := [];
        var visited: set<TreeNode> := {};
        var unvisited: set<TreeNode> := root.repr;
        assert |unvisited| == |root.repr|;
        var parents: seq<TreeNode> := [];
        var parentIndices: seq<int> := [];
        while |stack| > 0 
            invariant toSet(result) == visited
            invariant |parents| == |parentIndices|
            invariant forall x :: x in parents ==> x.Valid()
            invariant forall x :: x in stack ==> x.Valid()
            invariant forall x :: x in stack ==> x in root.repr
            invariant forall x :: x in visited ==> x in root.repr
            invariant unvisited !! visited
            invariant unvisited + visited == root.repr
            invariant visited <= root.repr
            invariant |visited| <= |root.repr|

            invariant forall x :: x in stack ==> x in unvisited
            invariant AllDisjoint(stack)
            invariant unvisited == TreeUnion(stack)
            invariant i == |result|
            invariant i == |visited|
            invariant 0 <= i <= |pro|
            invariant result == pro[..i]
            invariant |stack| > 0 && i < |pro| ==> stack[|stack|-1] == pro[i]
            decreases |root.repr| - i
        {
            print "i: ", i, "\n";
            print "pre ", "result ", mapNodes(result), " \n";
            print "pre ", "stack ", mapNodes(stack), " \n";
            print "pre ", "parents ", mapNodes(parents), " \n";
            print "pre ", "parentIndices ", parentIndices, " \n";
            var current := stack[|stack|-1];
            expect parents != [] ==> stackPred2(stack, parents, visited), "Before stack pred is true";
            print "pre ", "current ", current.val, "\n";
            var stack' := childStack(current);
            if |stack'| > 0 {
                parentIndices := parentIndices + [i];
                parents := parents + parentStack(current);
            }
            expect AllAncestors(parents), "Before stack AllAncestors true";
            assert children(current) <= current.repr;
            TreeUnionMaint(stack, current, unvisited);
            AllDisjointMaint(stack, current);

            ChildNodesAreValid(root, current);
            assert stack == stack[..|stack|-1]+[stack[|stack|-1]];
            assert forall x :: x in stack[..|stack|-1]+stack' ==> x.Valid() by {
              forall x | x in stack[..|stack|-1]+stack'
                ensures x.Valid()
              {
                if x in stack[..|stack|-1] {
                  assert x in stack;
                }else{
                  assert x in stack';
                }
              }
            }
            assert forall x :: x in stack[..|stack|-1]+stack' ==> x in unvisited-{current} by {
              forall x | x in stack[..|stack|-1]+stack'
                ensures x in unvisited-{current}
              {
                if x in stack[..|stack|-1] {
                  assert x in stack;
                  assert x != current;
                  assert x in unvisited-{current};
                }else{
                  TreeUnionConcat(stack[..|stack|-1],[stack[|stack|-1]]);
                  assert TreeUnion([stack[|stack|-1]]) == current.repr;
                  assert children(current) < current.repr;
                  assert x in children(current);
                  assert x != current;
                  childStackLemma(current);
                  TreeUnionConcat(stack[..|stack|-1],stack');
                  assert TreeUnion(stack') == current.repr-{current};
                  assert x in unvisited-{current};
                }
              }
            }
            stack := stack[..|stack|-1]+stack';
            result := result + [current];
            visited := visited + {current};
            unvisited := unvisited-{current};
            // if |parents| > 0 { 
            //   var childnodes := SetToSeq(children(parents[|parents|-1]));
            //   print "children, ", mapNodes(childnodes);
            // }
            parents := pruneParents(parents, visited);
          
            // if (|parents| > 0) && (children(parents[|parents|-1]) <= visited)
            // {
            //     parents := parents[..|parents|-1];
            //     // parentIndices := parentIndices[..|parentIndices|-1];
            // }

            // if (|parents| > 0) && (children(parents[|parents|-1]) <= visited)
            // {
            //     parents := parents[..|parents|-1];
            //     // parentIndices := parentIndices[..|parentIndices|-1];
            // }
            assume {:axiom} forall p :: p in parents ==> p.Valid();
         

            print "post ", "result ", mapNodes(result), " \n";
            print "post ", "stack ", mapNodes(stack), " \n";
            print "post ", "parents ", mapNodes(parents), " \n";
            print "post ", "parentIndices ", parentIndices, " \n";
            expect parents != [] ==> stackPred2(stack, parents, visited), "After pred works";
            expect AllAncestors(parents), "after stack AllAncestors true";
            i := i + 1;
        }
        assert result == PreorderTraversal(root)[0..|PreorderTraversal(root)|];
        return result;
    }

    method Main() 
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