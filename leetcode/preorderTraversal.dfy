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

    lemma childrenLemma(node: TreeNode)
        requires node.Valid()
        ensures children(node) < node.repr
        ensures node !in children(node)
    {

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

    function rightStackUnvisited(node: TreeNode, visited: set<TreeNode>): seq<TreeNode> 
        reads node
        // requires node.Valid()
    {
      if node.right != null && node.right !in visited then [node.right] else []
    }

    lemma rightStackUnvisitedLemma(node: TreeNode, visited: set<TreeNode>)
      ensures rightStackUnvisited(node, visited) != [] ==> |rightStackUnvisited(node, visited)| == 1
    {

    }

    predicate leftStackVisited(node: TreeNode, visited: set<TreeNode>) 
      reads node
    {
      if node.left != null then node.left in visited else true
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

    lemma pruneParentsLemma2(ss: seq<TreeNode>, visited: set<TreeNode>)
      requires AllAncestors(ss)
      requires ss!=[]
      requires pruneParents(ss, visited) == []
      ensures forall x: TreeNode :: x in ss && x !in pruneParents(ss, visited) ==> children(x) <= visited
    {
      if ss == [] {

      }else if |ss| == 1 {
        assert ss[0] in ss;
        if children(ss[0])<= visited {
          assert ss[0] !in  pruneParents(ss, visited);
        }else{
          assert ss[0] in  pruneParents(ss, visited);
        }
      }else{

      }
    }

    lemma newStackNotEmptyImpliesParentsNotEmpty(parents: seq<TreeNode>, stack: seq<TreeNode>, visited: set<TreeNode>, unvisited: set<TreeNode>)
      requires allLeftVisited(parents, visited)
      requires stack != []
      requires parents != []
      requires parents != [] ==> childOf(stack[ |stack| -1], parents[ |parents| -1])
      requires forall x :: x in parents ==> x.Valid()
      requires forall x :: x in stack ==> x.Valid()
      requires unvisited !! visited
      requires forall x :: x in stack ==> x in unvisited
      requires AllAncestors(parents)
      requires AllDisjoint(stack)
      requires unvisited == TreeUnion(stack)
      // requires pruneParents(parents+parentStack(stack[|stack|-1]), visited+{stack[|stack|-1]}) == []
      requires stack == allRight(parents, visited)
      requires forall x :: x in stack ==> x.Valid()
      ensures (stack[..|stack|-1] + childStack(stack[ |stack|-1]) != []) ==> pruneParents(parents+parentStack(stack[|stack|-1]), visited+{stack[|stack|-1]}) != []
    {
      if pruneParents(parents+parentStack(stack[|stack|-1]), visited+{stack[|stack|-1]}) == [] {
        parentsEmptyImplyStackEmpty(parents, stack, visited, unvisited);

      }

    }

    lemma parentsEmptyImplyStackEmpty(parents: seq<TreeNode>, stack: seq<TreeNode>, visited: set<TreeNode>, unvisited: set<TreeNode>)
      requires stack != []
      requires parents != []
      requires parents != [] ==> childOf(stack[ |stack| -1], parents[ |parents| -1])
      requires forall x :: x in parents ==> x.Valid()
      requires forall x :: x in stack ==> x.Valid()
      requires unvisited !! visited
      requires forall x :: x in stack ==> x in unvisited
      requires AllAncestors(parents)
      requires AllDisjoint(stack)
      requires unvisited == TreeUnion(stack)
      requires pruneParents(parents+parentStack(stack[|stack|-1]), visited+{stack[|stack|-1]}) == []
      // requires allLeftVisited(parents, visited)
      requires stack == allRight(parents, visited)
      ensures stack[..|stack|-1]+childStack(stack[|stack|-1]) == []

    {
      var current := stack[|stack|-1];
        pruneParentsLemma2(parents+parentStack(stack[|stack|-1]), visited+{stack[|stack|-1]});
        assert forall x :: x in parents+parentStack(stack[|stack|-1]) ==> children(x) <= visited+{current};
        if parentStack(stack[|stack|-1]) != [] {
          assert children(current) <= visited+{current};
          TreeUnionLemma(stack);
          // assert forall x :: x in children(current) ==> x in current.repr && x in unvisited && x !in visited+{current};
          childrenLemma(current);
          // assert forall x :: x in children(current) ==> x in current.repr && x in unvisited;
          assert forall x :: x in children(current) ==> x in current.repr;
          assert forall x :: x in children(current) ==> x in unvisited by {
            forall x | x in children(current)
              ensures x in unvisited
            {
              TreeUnionLemma2(stack, current, x);
            }
          }
          assert false;
        }
        assert parents+parentStack(stack[|stack|-1])  == parents;
        // assert visited+{stack[|stack|-1]} == root.repr;
        assert childStack(stack[|stack|-1]) == [];
        assert stack[..|stack|-1] == [] by {
          if stack[..|stack|-1] != [] {
            if stack == allRight(parents, visited) {
              allRightLemma(parents, visited);
              assert stack == stack[..|stack|-1]+[current];
              forall x | x in stack 
                ensures x in visited+{current}
              {
                var i :| 0 <= i < |parents| && x in rightStackUnvisited(parents[i], visited);
                assert x in children(parents[i]);
                assert parents[i] in parents;
                assert children(parents[i]) <= visited + {current};
              }
              assert visited !! unvisited;
              forall x | x in stack[..|stack|-1] 
                ensures x in visited
              {
                assert x in stack;
                assert x in unvisited;
                assert x in visited;

              }
              var somex :| somex in stack[..|stack|-1];
              assert somex in visited;
              assert false;
            } else if stack == allRightPlusChildren(parents, visited) {
              allRightPlusChildrenLemma(parents, visited);
              var somex :| somex in stack[..|stack|-1];
              assert somex in visited;
              assert false;
            }
          }
        }
        assert stack[..|stack|-1]+childStack(stack[|stack|-1]) == [];
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

  lemma AllAncestorsLemma(ts: seq<TreeNode>, i: int, j : int)
    requires forall x :: x in ts ==> x.Valid()
    requires AllAncestors(ts)
    requires 0 <=i < j < |ts|
    ensures ts[j].repr < ts[i].repr
    ensures ts[j] in ts[i].repr
  {
    // assert childOf(ts[j], ts[j-1]);
    assert ts[j-1] in ts;
    assert ts[j] in ts[j-1].repr;
    if j-1 > i {

    AllAncestorsLemma(ts, i, j-1);
    assert ts[j-1] in ts;
    // assert ts[j-1].repr
    }else{

    }
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

    lemma PreorderTraversalSlices(root: TreeNode)
      requires root.Valid()
      // ensures root.left != null && root.right != null ==> PreorderTraversal(root)[]
      ensures PreorderTraversal(root)[..1] == [root]
      ensures root.left != null ==> PreorderTraversal(root)[1..|PreorderTraversal(root.left)|+1] == PreorderTraversal(root.left)
      ensures root.right != null && root.left == null ==> PreorderTraversal(root)[1..|PreorderTraversal(root.right)|+1] == PreorderTraversal(root.right)
      ensures root.right != null && root.left != null ==> PreorderTraversal(root)[|PreorderTraversal(root.left)|+1..] == PreorderTraversal(root.right)
    {

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

    lemma TreeUnionMaint(stack: seq<TreeNode>, current: TreeNode, unvisited: set<TreeNode>)
        requires |stack| > 0
        requires unvisited == TreeUnion(stack)
        requires AllDisjoint(stack)
        requires forall x :: x in stack ==> x.Valid()
        requires current == stack[|stack|-1]
        ensures TreeUnion(stack[..|stack|-1]+childStack(current)) == unvisited-{current}
    {
        childStackLemma(current);
        assert current in stack;
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

    lemma {:verify } {:vcs_split_on_every_assert} FlatMapVisitedARN(stack: seq<TreeNode>, parents: seq<TreeNode>, visited: set<TreeNode>, unvisited: set<TreeNode>, current: TreeNode, newStack: seq<TreeNode>, newParents: seq<TreeNode>)
      requires |stack| > 0 
      requires current == stack[|stack|-1]
      requires current !in visited
      requires current.Valid()
      requires AllDisjoint(stack)
      requires forall x :: x in parents ==> x.Valid() && x in visited
      requires forall x :: x in stack ==> x.Valid()
      requires forall x :: x in stack ==> x in unvisited
      requires unvisited !! visited
      requires unvisited == TreeUnion(stack)
      requires AllAncestors(parents)
      requires |parents| > 0
      requires parents != [] ==> childOf(stack[ |stack| -1], parents[ |parents| -1])
      requires childStack(current) == []
      requires allLeftVisited(parents, visited)
      requires stack == Seq.Flatten(Seq.Map((x: TreeNode) reads x => rightStackUnvisited(x, visited), parents))

      requires newParents == pruneParents(parents+parentStack(stack[|stack|-1]), visited+{stack[|stack|-1]})
      requires newStack == stack[..|stack|-1] + childStack(stack[ |stack|-1])
      ensures stackPred2(newStack, newParents, visited+{current})
    {
      assert parentStack(current) == [];
      assert allRight(parents, visited) == stack;
      assert parents+parentStack(current) == parents;
      assert rightStackUnvisited(parents[ |parents| -1], visited) == [stack[ |stack| - 1]] by {
        var ms := Seq.Map((x: TreeNode) reads x => rightStackUnvisited(x, visited), parents);
        assert ms == ms[..|ms|-1]+[rightStackUnvisited(parents[ |parents| -1], visited)];
        Seq.LemmaFlattenConcat(ms[..|ms|-1],[rightStackUnvisited(parents[ |parents| -1], visited)]);
        assert stack == Seq.Flatten(ms[..|ms|-1])+Seq.Flatten([rightStackUnvisited(parents[ |parents| -1], visited)]);
        assert Seq.Flatten([rightStackUnvisited(parents[ |parents| -1], visited)]) == rightStackUnvisited(parents[ |parents| -1], visited);
        assert rightStackUnvisited(parents[ |parents| -1], visited) != [] by {
          assert childOf(stack[|stack|-1], parents[|parents|-1]);
          if stack[|stack|-1] == parents[|parents|-1].left {
            allRightLemma(parents, visited);
            assert stack[|stack|-1] in allRight(parents, visited);
            var i :| 0 <= i < |parents| && stack[|stack|-1] in rightStackUnvisited(parents[i], visited);
            assert  parents[|parents|-1].left != null;
            assert parents[|parents|-1] in parents;
            assert parents[i] in parents;
            assert parents[i].Valid();
            assert stack[|stack|-1] in parents[|parents|-1].repr;
            if i != |parents|-1 {
              // assert stack []
              if rightStackUnvisited(parents[ |parents| -1], visited) == [] {
                // assume parents[|parents|-1] in parents[i].repr; 
                AllAncestorsLemma(parents, i, |parents|-1);
                assert stack[|stack|-1] == parents[i].right;
                assert parents[i].right != null;
                
                if parents[|parents|-1] in parents[i].right.repr {
                  assert parents[|parents|-1] in visited && parents[|parents|-1] in unvisited;
                } else if parents[i].left != null && parents[|parents|-1] in parents[i].left.repr {
                  childChildrenInRootRepr(parents[i].left, parents[|parents|-1]);
                  assert parents[|parents|-1].repr < parents[i].left.repr;
                  assert stack[|stack|-1] in parents[i].left.repr && stack[|stack|-1] in parents[i].right.repr;
                  assert !parents[i].Valid();
                }else {
                  assert parents[|parents|-1] !in parents[i].right.repr;
                  assert parents[i].left == null || parents[|parents|-1] !in parents[i].left.repr;
                  assert (parents[i].repr == {parents[i]}+parents[i].left.repr + parents[i].right.repr) || (parents[i].repr == {parents[i]} + parents[i].right.repr);
                  assert parents[|parents|-1] == parents[i];
                  assert !parents[i].Valid();
                }

                // assert allRight(parents, visited) != stack;
                assert false;

              }else{
                rightStackUnvisitedLemma(parents[ |parents| -1], visited);
                assert rightStackUnvisited(parents[ |parents| -1], visited) != [];
                assert |rightStackUnvisited(parents[ |parents| -1], visited)| == 1;
                assert |stack| == |Seq.Flatten(ms[..|ms|-1])| + 1;
                assert parents[i] in parents;
                assert stack[|stack|-1] == parents[i].right;
                assert stack[|stack|-1] in parents[i].repr;
                assert i < |parents|-1;
                assert parents[i] in parents[..|parents|-1];
                //assert allRight(parents[..|parents|-1], visited);
                // var k :| 0 <= k < |parents|-1 && parents[..|parents|-1][k] == parents[i];
                assert stack[|stack|-1] in Seq.Flatten(ms[..|ms|-1]);
                // flattenLemma(ms[..|ms|-1], stack[|stack|-1]);
                var k :| 0 <= k < |Seq.Flatten(ms[..|ms|-1])| && Seq.Flatten(ms[..|ms|-1])[k] == stack[|stack|-1];
                assert stack[k] == stack[|stack|-1];

                assert !AllDisjoint(stack);
              }
            assert false;
            }else{
              assert stack[|stack|-1] !in rightStackUnvisited(parents[i], visited);
            assert false;
            }
            assert false;
          }
        }
      }
      assert newStack == stack[..|stack|-1];
      assert stack[ |stack| - 1] == parents[ |parents| -1].right;
      if newStack == [] {
      assume newParents == [];
      assert newStack  == allRight(newParents, visited+{current});
      assert allLeftVisited(newParents, visited+{current});

      }else{
        newStackNotEmptyImpliesParentsNotEmpty(parents, stack, visited, unvisited);
        assert newParents != [];
        assert newStack != [];
      assert newStack  == allRight(newParents, visited+{current}) by {
        forall x | x in newParents 
          ensures x in parents
        {

          }
      }
      assert allLeftVisited(newParents, visited+{current});
      }
    }

    lemma {:verify false} FlatMapVisitedARL(stack: seq<TreeNode>, parents: seq<TreeNode>, visited: set<TreeNode>, current: TreeNode, newStack: seq<TreeNode>, newParents: seq<TreeNode>)
      requires |stack| > 0 
      requires current == stack[|stack|-1]
      requires current !in visited
      requires current.Valid()
      requires forall parent :: parent in parents ==> parent.Valid()
      requires stack == allRight(parents, visited)
      requires newParents == pruneParents(parents+parentStack(stack[|stack|-1]), visited+{stack[|stack|-1]})
      requires newStack == stack[..|stack|-1] + childStack(stack[ |stack|-1])
      requires childStack(current) == [current.left]
      ensures stackPred2(newStack, newParents, visited+{current})
    {
    }

    lemma {:verify false} FlatMapVisitedARR(stack: seq<TreeNode>, parents: seq<TreeNode>, visited: set<TreeNode>, current: TreeNode, newStack: seq<TreeNode>, newParents: seq<TreeNode>)
      requires |stack| > 0 
      requires current == stack[|stack|-1]
      requires current !in visited
      requires current.Valid()
      requires forall parent :: parent in parents ==> parent.Valid()
      requires stack == allRight(parents, visited)
      requires newParents == pruneParents(parents+parentStack(stack[|stack|-1]), visited+{stack[|stack|-1]})
      requires newStack == stack[..|stack|-1] + childStack(stack[ |stack|-1])
      requires childStack(current) == [current.right]
      ensures stackPred2(newStack, newParents, visited+{current})
    {
    }

    lemma {:verify false} FlatMapVisitedARBoth(stack: seq<TreeNode>, parents: seq<TreeNode>, visited: set<TreeNode>, current: TreeNode, newStack: seq<TreeNode>, newParents: seq<TreeNode>)
      requires |stack| > 0 
      requires current == stack[|stack|-1]
      requires current !in visited
      requires current.Valid()
      requires forall parent :: parent in parents ==> parent.Valid()
      requires stack == allRight(parents, visited)
      requires newParents == pruneParents(parents+parentStack(stack[|stack|-1]), visited+{stack[|stack|-1]})
      requires newStack == stack[..|stack|-1] + childStack(stack[ |stack|-1])
      requires childStack(current) == [current.right, current.left]
      ensures stackPred2(newStack, newParents, visited+{current})
    {
    }

    lemma {:verify false} FlatMapVisitedPCN(stack: seq<TreeNode>, parents: seq<TreeNode>, visited: set<TreeNode>, current: TreeNode, newStack: seq<TreeNode>, newParents: seq<TreeNode>)
      requires |stack| > 0 
      requires current == stack[|stack|-1]
      requires current !in visited
      requires current.Valid()
      requires parents != []
      requires forall parent :: parent in parents ==> parent.Valid()
      requires stack == allRightPlusChildren(parents, visited)
      requires newParents == pruneParents(parents+parentStack(stack[|stack|-1]), visited+{stack[|stack|-1]})
      requires newStack == stack[..|stack|-1] + childStack(stack[ |stack|-1])
      requires childStack(current) == []
      ensures stackPred2(newStack, newParents, visited+{current})
    {
    }

    lemma {:verify false} FlatMapVisitedPCL(stack: seq<TreeNode>, parents: seq<TreeNode>, visited: set<TreeNode>, current: TreeNode, newStack: seq<TreeNode>, newParents: seq<TreeNode>)
      requires |stack| > 0 
      requires current == stack[|stack|-1]
      requires current !in visited
      requires current.Valid()
      requires parents != []
      requires forall parent :: parent in parents ==> parent.Valid()
      requires stack == allRightPlusChildren(parents, visited)
      requires newParents == pruneParents(parents+parentStack(stack[|stack|-1]), visited+{stack[|stack|-1]})
      requires newStack == stack[..|stack|-1] + childStack(stack[ |stack|-1])
      requires childStack(current) == [current.left]
      ensures stackPred2(newStack, newParents, visited+{current})
    {
    }

    lemma {:verify false} FlatMapVisitedPCR(stack: seq<TreeNode>, parents: seq<TreeNode>, visited: set<TreeNode>, current: TreeNode, newStack: seq<TreeNode>, newParents: seq<TreeNode>)
      requires |stack| > 0 
      requires current == stack[|stack|-1]
      requires current !in visited
      requires current.Valid()
      requires parents != []
      requires forall parent :: parent in parents ==> parent.Valid()
      requires stack == allRightPlusChildren(parents, visited)
      requires newParents == pruneParents(parents+parentStack(stack[|stack|-1]), visited+{stack[|stack|-1]})
      requires newStack == stack[..|stack|-1] + childStack(stack[ |stack|-1])
      requires childStack(current) == [current.right]
      ensures stackPred2(newStack, newParents, visited+{current})
    {
    }

    lemma {:verify false} FlatMapVisitedPCBoth(stack: seq<TreeNode>, parents: seq<TreeNode>, visited: set<TreeNode>, current: TreeNode, newStack: seq<TreeNode>, newParents: seq<TreeNode>)
      requires |stack| > 0 
      requires current == stack[|stack|-1]
      requires current !in visited
      requires current.Valid()
      requires parents != []
      requires forall parent :: parent in parents ==> parent.Valid()
      requires stack == allRightPlusChildren(parents, visited)
      requires newParents == pruneParents(parents+parentStack(stack[|stack|-1]), visited+{stack[|stack|-1]})
      requires newStack == stack[..|stack|-1] + childStack(stack[ |stack|-1])
      requires childStack(current) == [current.right, current.left]
      ensures stackPred2(newStack, newParents, visited+{current})
    {
    }

    lemma {:verify false} {:vcs_split_on_every_assert} traverseMaint2(
        root: TreeNode,
        result: seq<TreeNode>,
        visited: set<TreeNode>,
        stack: seq<TreeNode>,
        parents: seq<TreeNode>,
        unvisited: set<TreeNode>,
        newStack: seq<TreeNode>,
        newParents: seq<TreeNode>,
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
      requires forall x :: x in stack ==> x in unvisited
      requires AllDisjoint(stack)
      requires unvisited == TreeUnion(stack)
      requires i == |result|
      requires 0 <= i <= |PreorderTraversal(root)|
      requires result == PreorderTraversal(root)[..i]
      requires newParents == pruneParents(parents+parentStack(stack[|stack|-1]), visited+{stack[|stack|-1]})
      requires newStack == stack[..|stack|-1]+childStack(stack[|stack|-1])
      requires parents != [] && newParents != [] ==> stackPred2(newStack, newParents, visited+{stack[|stack|-1]}) 
      requires |stack| > 0 && i < |PreorderTraversal(root)| ==> stack[|stack|-1] == PreorderTraversal(root)[i]
      ensures result+[] == PreorderTraversal(root)[..i]
      ensures |newStack| > 0 && i+1 < |PreorderTraversal(root)| ==> newStack[ |newStack|-1] == PreorderTraversal(root)[i+1]
    {
      if |newStack| > 0 && i+1 < |PreorderTraversal(root)| {
        if newStack == allRight(newParents, visited+{stack[|stack|-1]}) {

          assert newStack[ |newStack|-1] == PreorderTraversal(root)[i+1];
        } else if |newParents| > 0 && newStack == allRightPlusChildren(newParents, visited+{stack[|stack|-1]}) {

          assert newStack[ |newStack|-1] == PreorderTraversal(root)[i+1];
        }
      }  
    }

    lemma {:verify } {:vcs_split_on_every_assert} traverseMaint(
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
      requires forall x :: x in stack ==> x in unvisited
      requires AllDisjoint(stack)
      requires unvisited == TreeUnion(stack)
      // requires i == |result|
      // requires 0 <= i <= |PreorderTraversal(root)|
      // requires result == PreorderTraversal(root)[..i]
      // requires |stack| > 0 && i < |PreorderTraversal(root)| ==> stack[|stack|-1] == PreorderTraversal(root)[i]
      ensures AllAncestors(pruneParents(parents+parentStack(stack[|stack|-1]), visited+{stack[|stack|-1]}))
      ensures forall x :: x in pruneParents(parents+parentStack(stack[|stack|-1]), visited+{stack[|stack|-1]}) ==> x.Valid()
      // ensures parents != [] && pruneParents(parents+parentStack(stack[|stack|-1]), visited+{stack[|stack|-1]}) != [] ==> stackPred2(stack[..|stack|-1]+childStack(stack[|stack|-1]), pruneParents(parents+parentStack(stack[|stack|-1]), visited+{stack[|stack|-1]}), visited+{stack[|stack|-1]})
      ensures parents != [] && pruneParents(parents+parentStack(stack[|stack|-1]), visited+{stack[|stack|-1]}) == [] ==> stack[..|stack|-1]+childStack(stack[|stack|-1]) == []
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
      var newParents := pruneParents(parents+parentStack(stack[|stack|-1]), visited+{stack[|stack|-1]});
      var newStack := stack[..|stack|-1]+childStack(stack[|stack|-1]);
      var current := stack[|stack|-1];
      if parents != [] {
      if newParents != []  {
        if |childStack(stack[|stack|-1])| > 0 {
          assert parentStack(stack[|stack|-1]) == [stack[|stack|-1]];
        }else{
          assert parentStack(stack[|stack|-1]) == [];
        }
        // assert childOf(newStack[|newStack|-1], newParents[|newParents|-1]);
        // assert stackPred2(newStack, newParents, visited+{current}) by {
        //   childStackLemma(current);
        //   var visitMap := (x: TreeNode) reads x => rightStackUnvisited(x, visited);
        //   var newVisitMap := (x: TreeNode) reads x => rightStackUnvisited(x, visited+{current});
        //   if stack == allRight(parents, visited) {
        //     if childStack(current) == [current.right, current.left] {
        //       FlatMapVisitedARBoth(stack, parents, visited, current, newStack, newParents);
        //     }else if  childStack(current) == [current.left] {
        //       FlatMapVisitedARL(stack, parents, visited, current, newStack, newParents);

        //     }else if childStack(current) == [current.right] {
        //       FlatMapVisitedARR(stack, parents, visited, current, newStack, newParents);
        //     }else if childStack(current) == [] {
        //       FlatMapVisitedARN(stack, parents, visited, unvisited, current, newStack, newParents);
        //       assert newStack == Seq.Flatten(Seq.Map(newVisitMap, newParents));
        //       assert stackPred2(newStack, newParents, visited+{current});
        //     }
        //   }else if |parents| > 0 && stack == allRightPlusChildren(parents, visited) {
        //     if childStack(current) == [current.right, current.left] {
        //       FlatMapVisitedPCBoth(stack, parents, visited, current, newStack, newParents);
        //     }else if  childStack(current) == [current.left] {
        //       FlatMapVisitedPCL(stack, parents, visited, current, newStack, newParents);
        //     }else if childStack(current) == [current.right] {
        //       FlatMapVisitedPCR(stack, parents, visited, current, newStack, newParents);
        //     }else if childStack(current) == [] {
        //       FlatMapVisitedPCN(stack, parents, visited, current, newStack, newParents);
        //     }
        //   }
        // }
      }
      }

      if parents != [] && pruneParents(parents+parentStack(stack[|stack|-1]), visited+{stack[|stack|-1]}) == [] {
        // assert TreeUnion(stack[|stack|-1]);
        pruneParentsLemma2(parents+parentStack(stack[|stack|-1]), visited+{stack[|stack|-1]});
        assert forall x :: x in parents+parentStack(stack[|stack|-1]) ==> children(x) <= visited+{current};
        if parentStack(stack[|stack|-1]) != [] {
          assert children(current) <= visited+{current};
          TreeUnionLemma(stack);
          // assert forall x :: x in children(current) ==> x in current.repr && x in unvisited && x !in visited+{current};
          childrenLemma(current);
          // assert forall x :: x in children(current) ==> x in current.repr && x in unvisited;
          assert forall x :: x in children(current) ==> x in current.repr;
          assert forall x :: x in children(current) ==> x in unvisited by {
            forall x | x in children(current)
              ensures x in unvisited
            {
              TreeUnionLemma2(stack, current, x);
            }
          }
          assert false;
        }
        assert parents+parentStack(stack[|stack|-1])  == parents;
        // assert visited+{stack[|stack|-1]} == root.repr;
        assert childStack(stack[|stack|-1]) == [];
        assert stack[..|stack|-1] == [] by {
          if stack[..|stack|-1] != [] {
            if stack == allRight(parents, visited) {
              allRightLemma(parents, visited);
              assert stack == stack[..|stack|-1]+[current];
              forall x | x in stack 
                ensures x in visited+{current}
              {
                var i :| 0 <= i < |parents| && x in rightStackUnvisited(parents[i], visited);
                assert x in children(parents[i]);
                assert parents[i] in parents;
                assert children(parents[i]) <= visited + {current};
              }
              assert visited !! unvisited;
              forall x | x in stack[..|stack|-1] 
                ensures x in visited
              {
                assert x in stack;
                assert x in unvisited;
                assert x in visited;

              }
              var somex :| somex in stack[..|stack|-1];
              assert somex in visited;
              assert false;
            } else if stack == allRightPlusChildren(parents, visited) {
              allRightPlusChildrenLemma(parents, visited);
              var somex :| somex in stack[..|stack|-1];
              assert somex in visited;
              assert false;
            }
          }
        }
        assert stack[..|stack|-1]+childStack(stack[|stack|-1]) == [];
      }
    }

    predicate stackPred(stack: seq<TreeNode>, parents: seq<TreeNode>) 
      reads parents, set i | 0 <= i < |parents| :: parents[i], reprUnion(parents)
      requires forall parent :: parent in parents ==> parent.Valid()
    {
      stack == Seq.Flatten(Seq.Map(rightStack, parents)) || (|parents| > 0 && stack == Seq.Flatten(Seq.Map(rightStack, parents[..|parents|-1]))+childStack(parents[|parents|-1]))
    }

    function allRight(parents: seq<TreeNode>, visited: set<TreeNode>): seq<TreeNode> 
      reads parents, set i | 0 <= i < |parents| :: parents[i], reprUnion(parents)
    {
      var visitMap := (x: TreeNode) reads x => rightStackUnvisited(x, visited);
      Seq.Flatten(Seq.Map(visitMap, parents))
    }

    lemma flattenLemma<T>(xs: seq<seq<T>>, x: T)
      requires x in Seq.Flatten(xs)
      ensures x in Seq.Flatten(xs) ==> exists xx :: xx in xs && x in xx
    {
      if |xs| == 1 {
        assert xs[0] in xs;
        if x in xs[0] {

        }else {
          assert x !in xs[0];
          assert x in Seq.Flatten(xs);
          assert xs[1..] == [];
          assert Seq.Flatten(xs) == xs[0];
          assert false;
        }
      }else{
        assert xs == [xs[0]] + xs[1..];
        Seq.LemmaFlattenConcat([xs[0]], xs[1..]);
        if x in xs[0] {

        }else {
          flattenLemma(xs[1..], x);
        }

      }
    }

    lemma allRightLemma(parents: seq<TreeNode>, visited: set<TreeNode>)
      ensures forall x :: x in allRight(parents, visited) ==> exists i :: 0 <= i < |parents| && x in rightStackUnvisited(parents[i], visited)
    {
      forall x | x in allRight(parents, visited)
        ensures exists i :: 0 <= i < |parents| && x in rightStackUnvisited(parents[i], visited)
      {
      var visitMap := (x: TreeNode) reads x => rightStackUnvisited(x, visited);
        assert forall  k :: 0 <= k < |parents| ==> Seq.Map(visitMap, parents)[k] == rightStackUnvisited(parents[k], visited);
        flattenLemma(Seq.Map(visitMap, parents), x);
      }
    }

    function allRightPlusChildren(parents: seq<TreeNode>, visited: set<TreeNode>): seq<TreeNode>
      reads parents, set i | 0 <= i < |parents| :: parents[i], reprUnion(parents)
      requires |parents| > 0
      requires forall parent :: parent in parents ==> parent.Valid()
    {
      var visitMap := (x: TreeNode) reads x => rightStackUnvisited(x, visited);
      Seq.Flatten(Seq.Map(visitMap, parents[..|parents|-1]))+childStack(parents[|parents|-1])
    }

    lemma allRightPlusChildrenLemma(parents: seq<TreeNode>, visited: set<TreeNode>)
      requires |parents| > 0
      requires forall parent :: parent in parents ==> parent.Valid()
      ensures forall x :: x in allRightPlusChildren(parents, visited) ==> exists i :: 0 <= i < |parents| && x in children(parents[i])
    {
      forall x | x in allRightPlusChildren(parents, visited)
        ensures exists i :: 0 <= i < |parents| && x in children(parents[i])
      {
        //Seq.Flatten(Seq.Map(visitMap, parents[..|parents|-1]))+childStack(parents[|parents|-1])
        var visitMap := (x: TreeNode) reads x => rightStackUnvisited(x, visited);
        if x in Seq.Flatten(Seq.Map(visitMap, parents[..|parents|-1])) {
        allRightLemma(parents[..|parents|-1], visited);
        assert forall x :: x in allRight(parents[..|parents|-1], visited) ==> exists k :: 0 <= k < |parents[..|parents|-1]| && x in rightStackUnvisited(parents[..|parents|-1][k], visited);
        }else{
          assert x in childStack(parents[|parents|-1]);
          assert x in children(parents[|parents|-1]);
        }
      }
    }

    predicate allLeftVisited(parents: seq<TreeNode>, visited: set<TreeNode>) 
      reads parents, set i | 0 <= i < |parents| :: parents[i]
    {
      forall p :: p in parents ==> leftStackVisited(p, visited)
    }

    predicate allLeftReprVisited(parents: seq<TreeNode>, visited: set<TreeNode>) 
      reads parents, set i | 0 <= i < |parents| :: parents[i], set i | 0 <= i < |parents| :: parents[i].left
    {
      forall p :: p in parents ==> forall c :: c in (if p.left != null then p.left.repr else {}) ==> c in visited
    }

    predicate stackPred2(stack: seq<TreeNode>, parents: seq<TreeNode>, visited: set<TreeNode>) 
      reads parents, set i | 0 <= i < |parents| :: parents[i], reprUnion(parents)
      requires forall parent :: parent in parents ==> parent.Valid()
    {
      (stack == allRight(parents, visited) && allLeftVisited(parents, visited))
      || (|parents| > 0 && stack == allRightPlusChildren(parents, visited) && allLeftVisited(parents[..|parents|-1], visited))
    }

    /**
      This is the main algorithm I am trying to verify as iteratively equivalent to PreorderTraversal. 
      In it's basic form as it would be implemented in most languages it should be equivalent to TraverseBasic.
      However, to verify the algorithm many ghost variables are needed to show what the implicit relationships are 
      between the variables.

      To experiment with the invariants I have made the ghost variables real. I have also added print statements to 
      show the state of the variables at each iteration. Then the challenge is to inductively show the relationships
      between all the ghost variables are maintained.

      The overarching goal is the prove the following two invariants.
      pro is abbreviation for PreorderTraversal(root)
      invariant result == pro[..i]
      invariant |stack| > 0 && i < |pro| ==> stack[|stack|-1] == pro[i]

      If we can do this then Traverse will verify. Invariant 1 follows from invariant 2 so it is the real
      challenge. If we can define ghost variables and functions to inductively maintain them that imply invariant 2
      then we are done. 

      The most important ghost variables I have defined are parents, visited, unvisited, and the stack.
      The stack represents the list of unvisited nodes. The parents actually represent the call stack of functions.
      They are the nodes which represent the function call stack. The only true real variable is the result array/seq.

      invariant parents != [] ==> childOf(stack[ |stack| -1], parents[ |parents| -1])
      invariant AllAncestors(parents)
      invariant toSet(result) == visited
      invariant AllDisjoint(stack)
      invariant unvisited == TreeUnion(stack)
      invariant unvisited !! visited
      invariant unvisited + visited == root.repr

      The easiest properties to prove were AllDisjoint(stack). Essentially, all nodes currently on the stack and 
      their entire subtree have not been visited. The result array is the same set of nodes that have been visited.
      Therefore the unvisited and visited sets are disjoint and they always should sum to the original root repr or 
      node set. TreeUnion() basically collects all the repr/node sets of all the nodes in the stack and sums them together.
      That set should be the same as the unvisited set.

      There were a couple of choices about how to define the parents array. 
      I believe that pruneParents() will be the right function to represents the functional call stack. 
      parents' := pruneParents(parents+parentStack(stack[|stack|-1]), visited+{stack[|stack|-1]})

      The function parentStack will add the current node to the parent stack unless it does not have child nodes.
      Trying to verify this lead to another required property allLeftVisited and stackPred2. 

      allLeftVisited implies the stronger property that if we are at a given node then all the parent nodes on the way
      to the current node have already had their entire left subtree visited. allLeftReprVisited would be this property.

      stackPred2 basically says that for every parent in the parent sequence then only the right child will be on the stack
      unless that parent happens to be the very last node which was visited which put both it's left and right child on the
      if it had them. It would have been nice to use Seq.FlatMap but it seems to not be available in Dafny 4.6 despite being
      listed in the library.

      The tricky thing then is to prove things about Seq.Flatten(Seq.Map(visitmap, parents)) since visitMap will sometimes return an empty array.
      Basically proving that the stack equals Seq.Flatten(Seq.Map(visitmap, parents)) (seems easier)
      or the reverse the Seq.Flatten(Seq.Map(visitmap, parents)) != [] implies parents != [] (seems harder so far)

      I think this is an important property but I am uncertain if it gets us all the way there because it doesn't say anything about the relationship to
      i or the index of the parent to the current stack directly. To that end I started defining the parentIndices ghost variable to keep track of the parent's index in the result array.
      I have not defined a function to update it properly yet or to describe it's properties so far.


      // invariant |parents| == |parentIndices|
      // invariant forall k :: 0 <= k < |parentIndices| ==> result[parentIndices[k]] == parents[k]

      But essentially if the current node is being visited then the parent of the curent node will have position i-1 or
      we have just finshed off an entire left subtree and we have now went back up the subtree to some right node.
      Possibly at this point we can invoke the lemma PreorderTraversalSlices(). The current last parent should be the 
      parent of the currently visited right node. I think another property may need defined and proved that the last stack node
      is the deepest most unvisited node on the stack and it always will match up with the last parent node.
     */
    
    method {:verify false} {:vcs_split_on_every_assert} Traverse(root: TreeNode) returns (result: seq<TreeNode>)
        requires root.Valid()
        ensures result == PreorderTraversal(root)
    {
        //The stack of nodes to visit next
        var stack := [root];
        //the full preorder generated just for comparisons
        var pro := PreorderTraversal(root);
        assert |pro| == root.TreeSize();
        var i := 0;
        result := [];
        //This set will include all the TreeNodes that have been visited by the algorithm
        var visited: set<TreeNode> := {};
        //This set is all the nodes in Root's entire tree that have not been visited yet
        var unvisited: set<TreeNode> := root.repr;
        assert |unvisited| == |root.repr|;
        //These are the parent nodes for all the nodes currently in the stack (generally)
        //Specifically I think they should fulfill the predicate StackPred2
        // and they should form a path from root to the current node
        var parents: seq<TreeNode> := [];
        // This is an idea I was playing with but may not be going anywhere with
        // The idea here is that the indices of parent nodes in the preordertraversal might be useful to tell us something
        var parentIndices: seq<int> := [];
        while |stack| > 0 
            /*verifies */
            invariant toSet(result) == visited
            // invariant |parents| == |parentIndices|
            /*verifies */
            invariant i == |visited|
            /*verifies */
            invariant i == |result|
            /*verifies */
            invariant forall x :: x in parentIndices ==> x < i 
            // invariant forall k :: 0 <= k < |parentIndices| ==> result[parentIndices[k]] == parents[k]
            /*verifies */
            invariant forall x :: x in parents ==> x.Valid()
            /*verifies */
            invariant forall x :: x in stack ==> x.Valid()
            /*verifies */
            invariant forall x :: x in stack ==> x in root.repr
            /*verifies, might be redundant */
            invariant forall x :: x in visited ==> x in root.repr
            /*verifies */
            invariant unvisited !! visited
            /*verifies */
            invariant unvisited + visited == root.repr
            /*verifies, might be redundant */
            invariant visited <= root.repr
            /*verifies, might be redundant */
            invariant |visited| <= |root.repr|

            /*verifies */
            invariant forall x :: x in stack ==> x in unvisited
            /*verifies */
            invariant AllDisjoint(stack)
            /*verifies */
            invariant unvisited == TreeUnion(stack)
            /*verifies */
            invariant 0 <= i <= |pro|
            // invariant result == pro[..i]
            // invariant |stack| > 0 && i < |pro| ==> stack[|stack|-1] == pro[i]
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

method {:verify false} TraverseBasic(root: TreeNode) returns (result: seq<TreeNode>)
        requires root.Valid()
        ensures result == PreorderTraversal(root)
    {
        var stack := [root];
        while |stack| > 0 
        {
            var current := stack[|stack|-1];
            //The following was extracted into the function childStack();
            var stack' := [];
            if current.right != null {
                stack' := stack' + [current.right];
            }
            if current.left != null {
                stack' := stack' + [current.left];
            }
            stack := stack[..|stack|-1]+stack';
            result := result + [current];
        }
        return result;
    }


    /*
        By hitting F5 Dafny will attempt to run code in a Main method. You will need to add --standard-libraries to
        the run command to execute because of the imported flatten and map functions.

        This is very useful to test invariants.
        "expect" statements are the run time dual of "assert" statements. As in asserts task the verifier must test to be 
        true. Where as "expect" statements must be tested to be true during runtime.
    */
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
