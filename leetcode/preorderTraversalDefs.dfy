include "./invertTree.dfy"

module PreorderTraversalSupp {
    import opened InvertBinaryTree
    import Std.Collections.Seq
    //Functions && Predicates

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

    function rightStackUnvisited(node: TreeNode, visited: set<TreeNode>): seq<TreeNode> 
        reads node
        // requires node.Valid()
    {
      if node.right != null && node.right !in visited then [node.right] else []
    }

    predicate leftStackVisited(node: TreeNode, visited: set<TreeNode>) 
      reads node
    {
      if node.left != null then node.left in visited else true
    }
    // method

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
      reads (set i | 0 <= i < |ss| :: ss[i])
        ensures forall x :: x in pruneParents(ss, visited) ==> x in ss
    {
      if ss != [] then if children(ss[|ss|-1]) <= visited then pruneParents(ss[..|ss|-1], visited) else ss else []
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
    predicate stackPred2(stack: seq<TreeNode>, parents: seq<TreeNode>, visited: set<TreeNode>) 
      reads parents, set i | 0 <= i < |parents| :: parents[i], reprUnion(parents)
      requires forall parent :: parent in parents ==> parent.Valid()
    {
      (stack == allRight(parents, visited) && allLeftVisited(parents, visited))
      || (|parents| > 0 && stack == allRightPlusChildren(parents, visited) && allLeftVisited(parents[..|parents|-1], visited))
    }

    function allRightPlusChildren(parents: seq<TreeNode>, visited: set<TreeNode>): seq<TreeNode>
      reads parents, set i | 0 <= i < |parents| :: parents[i], reprUnion(parents)
      requires |parents| > 0
      requires forall parent :: parent in parents ==> parent.Valid()
    {
      var visitMap := (x: TreeNode) reads x => rightStackUnvisited(x, visited);
      Seq.Flatten(Seq.Map(visitMap, parents[..|parents|-1]))+childStack(parents[|parents|-1])
    }

    ghost predicate allValidParents(root: TreeNode, node: TreeNode) 
      reads root, root.repr, root.parentRepr, root.parent, node, node.repr, node.parentRepr, node.parent
      requires root.Valid()
      requires root.ParentValid()
      requires node.Valid()
      requires node.ParentValid()
    {
      forall x :: x in node.repr ==> x.parentRepr <= root.repr-x.repr && x.ParentValid() && (root != x ==> x.parent != null)
    }
    //Lemmas

    lemma childrenLemma(node: TreeNode)
        requires node.Valid()
        ensures children(node) < node.repr
        ensures node !in children(node)
    {}

    lemma rightStackUnvisitedLemma(node: TreeNode, visited: set<TreeNode>)
      ensures rightStackUnvisited(node, visited) != [] ==> |rightStackUnvisited(node, visited)| == 1
    {
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

    lemma parentStackLemma(node: TreeNode)
      requires node.Valid()
      ensures forall x :: x in parentStack(node) ==> x.Valid()
    {}

    lemma pruneParentsLemma(ss: seq<TreeNode>, visited: set<TreeNode>)
      requires AllAncestors(ss)
      ensures AllAncestors(pruneParents(ss, visited))
    {}

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

    lemma AllValidParentsChild(root: TreeNode, child: TreeNode) 
      requires root.Valid()
      requires root.ParentValid()
      requires allValidParents(root, root)
      requires child != root
      requires child in root.repr
      ensures child.Valid()
      ensures child.ParentValid()
    {
      ChildNodesReprAreLess(root, child);
      childInRootRepr(root, child);
    }

    lemma   parentsUniqueHelper(root: TreeNode, someNode: TreeNode,  parent: TreeNode, child: TreeNode)
      requires root.Valid()
      requires root.ParentValid()
      requires someNode in root.repr
      requires someNode != root
      requires someNode.Valid()
      requires someNode.ParentValid()
      requires allValidParents(root, someNode)
      requires parent in root.repr
      requires child in root.repr
      requires parent in someNode.repr
      requires child in someNode.repr
      requires child.parent != null
      requires child.parent != root
      requires child.parent in root.repr
      requires child.parent in someNode.repr
      requires child != root
      requires parent != child.parent
      requires parent != root
      requires childOf(child, parent)
      decreases someNode.repr
      ensures false
    {
      reveal child.ParentValid();

      assert child.parent != null;
      assert child.ParentValid();
      assert child.parentRepr == {child.parent} + child.parent.parentRepr;
      ChildNodesAreValid(root, child.parent);
      ChildNodesAreValid(root, parent);
      ChildNodesAreValid(root, child);
        if parent != someNode && child.parent != someNode {
          childInRootRepr(someNode, parent);
          ChildNodesAreValid(root, someNode);
          if someNode.left != null && someNode.right != null {
            if child.parent in someNode.left.repr && parent in someNode.right.repr {
              ChildNodesAreValid(parent, child);
              ChildNodesAreValid(child.parent, child);
              ChildNodesAreValid(someNode.left, child.parent);
              ChildNodesAreValid(someNode.right, parent);
              assert child in someNode.left.repr && child in someNode.right.repr;
              assert false;
            } else if child.parent in someNode.right.repr && parent in someNode.left.repr {
              ChildNodesAreValid(parent, child);
              ChildNodesAreValid(child.parent, child);
              ChildNodesAreValid(someNode.left, parent);
              ChildNodesAreValid(someNode.right, child.parent);
              assert child in someNode.left.repr && child in someNode.right.repr;
              assert false;
            } else if child.parent in someNode.right.repr && parent in someNode.right.repr {
              ChildNodesAreValid(parent, child);
              ChildNodesAreValid(someNode.right, child.parent);
              parentsUniqueHelper(root, someNode.right, parent, child);
              assert false;
            } else if child.parent in someNode.left.repr && parent in someNode.left.repr {
              ChildNodesAreValid(parent, child);
              ChildNodesAreValid(someNode.left, parent);
              parentsUniqueHelper(root, someNode.left, parent, child);
              assert false;
            }else{
              assert false;
            }
          } else if someNode.left == null && someNode.right != null {
              parentsUniqueHelper(root, someNode.right, parent, child);
              assert false;
          } else if someNode.left != null && someNode.right == null {
              parentsUniqueHelper(root, someNode.left, parent, child);
              assert false;
          }else{
            assert false;
          }

        }else if parent != someNode && child.parent == someNode {
          childInRootRepr(someNode, parent);
          if child.parent.left != null && child.parent.right != null {
            if child.parent.right == child && parent in child.parent.left.repr {
              ChildNodesAreValid(child.parent.left, parent);
              ChildNodesAreValid(parent, child);
              assert child in someNode.left.repr && child in someNode.right.repr;
              assert false;
            } else if child.parent.right == child && parent in child.parent.right.repr {
              assert false;
            } else if child.parent.left == child && parent in child.parent.right.repr {
              ChildNodesAreValid(child.parent.right, parent);
              ChildNodesAreValid(parent, child);
              assert child in someNode.left.repr && child in someNode.right.repr;
              assert false;
            } else if child.parent.left == child && parent in child.parent.left.repr {
              assert false;
            }else{
              assert false;
            }

          } else if child.parent.left == null && child.parent.right != null {
            assert child.parent.right == child;
            assert false;

          }else if child.parent.left != null && child.parent.right == null {
            assert child.parent.left == child;
            assert false;
          }else{
            assert false;
          }
        }else if parent == someNode && child.parent != someNode {
         if parent.left != null && parent.right != null {
            if parent.right == child && child.parent in parent.left.repr {
              ChildNodesAreValid(parent.left, child.parent);
              assert child in someNode.left.repr && child in someNode.right.repr;
              assert false;
            } else if parent.right == child && child.parent in parent.right.repr {
              assert false;
            } else if parent.left == child && child.parent in parent.right.repr {
              ChildNodesAreValid(parent.right, child.parent);
              assert child in someNode.left.repr && child in someNode.right.repr;
              assert false;
            } else if parent.left == child && child.parent in parent.left.repr {
              assert false;
            }else{
              assert false;
            }

          } else if parent.left == null && parent.right != null {
            assert parent.right == child;
            assert false;

          }else if parent.left != null && parent.right == null {
            assert parent.left == child;
            assert false;
          }else{
            assert false;
          }
          assert false;
        }else{
          assert parent == someNode && child.parent == someNode;
          assert false;
        }
        assert false;
    }

    lemma  parentsUniqueHelperRoot(root: TreeNode, parent: TreeNode, child: TreeNode)
      requires root.Valid()
      requires root.ParentValid()
      requires allValidParents(root, root)
      requires parent in root.repr
      requires child in root.repr
      requires child.parent != null
      requires child != root
      requires parent != child.parent
      requires child.parent == root
      requires parent != root
      requires childOf(child, parent)
      ensures false
    {
      reveal child.ParentValid();

      assert child.parent != null;
      assert child.ParentValid();
      assert child.parentRepr == {child.parent} + child.parent.parentRepr;

      ChildNodesAreValid(root, parent);
      assert parent.Valid();
     
      childInRootRepr(root, parent);
      if child == root.left {
        if root.right == null {

            assert parent in child.repr;
          assert false;
        }else{
          if parent in root.left.repr {
            assert parent in child.repr;

          }else if parent in root.right.repr {
            ChildNodesAreValid(root.right, parent);
            childChildrenInRootRepr(parent, child);
            assert child in root.right.repr;
            assert child in root.left.repr;
          }
    assert false;
        }
      }else if child == root.right {

        if root.left == null {

            assert parent in child.repr;
          assert false;
        }else{
          if parent in root.left.repr {
            assert child in root.right.repr;
            ChildNodesAreValid(root.left, parent);
            childChildrenInRootRepr(parent, child);
            assert child in root.left.repr;

          }else if parent in root.right.repr {
            assert parent in child.repr;
          }
    assert false;
        }
    assert false;
      }

    }
    
    lemma parentsUnique(root: TreeNode)
      requires root.Valid()
      requires root.ParentValid()
      requires allValidParents(root, root)
      decreases root.repr
      ensures forall parent, child :: child in root.repr && parent in root.repr && childOf(child, parent) ==> parent == child.parent
    {
      forall parent, child | child in root.repr && parent in root.repr && childOf(child, parent)
        ensures parent == child.parent
      {
        ChildNodesAreValid(root, parent);
        reveal child.ParentValid();
        assert child != root;
        if parent != child.parent {
          assert child in root.repr;
          assert child.parent != null;
          assert child.ParentValid();
          assert child.parentRepr == {child.parent} + child.parent.parentRepr;
          assert child.parent in child.parentRepr;
          assert child.parent in root.repr;
          assert childOf(child, child.parent);
          ChildNodesAreValid(root, child.parent);
          assert child.parent.Valid();
          assert child in child.parent.repr;
          assert child in parent.repr;
          if parent == root {
            childInRootRepr(root, child.parent);
            if child == root.left {
              if root.right == null {

                  assert child.parent in child.repr;
                assert false;
              }else{
                if child.parent in root.left.repr {
                  assert child.parent in child.repr;

                }else if child.parent in root.right.repr {
                  ChildNodesAreValid(root.right, child.parent);
                  childChildrenInRootRepr(child.parent, child);
                  assert child in root.right.repr;
                  assert child in root.left.repr;
                }
          assert false;
              }
            }else if child == root.right {

              if root.left == null {

                  assert child.parent in child.repr;
                assert false;
              }else{
                if child.parent in root.left.repr {
                  assert child in root.right.repr;
                  ChildNodesAreValid(root.left, child.parent);
                  childChildrenInRootRepr(child.parent, child);
                  assert child in root.left.repr;

                }else if child.parent in root.right.repr {
                  assert child.parent in child.repr;
                }
          assert false;
              }
          assert false;
            }
          }else{

            if child.parent == root {

            parentsUniqueHelperRoot(root, parent, child);
            }else{
              assert parent != root;
              assert child.parent != root;
              childInRootRepr(root, parent);
              childInRootRepr(root, child.parent);
              if root.left != null && root.right != null {
                if parent in root.left.repr && child.parent in root.right.repr {
                  ChildNodesAreValid(root.left, parent);
                  ChildNodesAreValid(root.right, child.parent);
                  assert child in root.left.repr && child in root.right.repr;
                assert false;
                } else if parent in root.right.repr && child.parent in root.left.repr {
                  ChildNodesAreValid(root.right, parent);
                  ChildNodesAreValid(root.left, child.parent);
                  assert child in root.left.repr && child in root.right.repr;
                assert false;
                } else if parent in root.left.repr && child.parent in root.left.repr {
                  ChildNodesAreValid(root.left, parent);
                 parentsUniqueHelper(root, root.left, parent, child);
                assert false;
                } else if parent in root.right.repr && child.parent in root.right.repr {
                  ChildNodesAreValid(root.right, parent);
                 parentsUniqueHelper(root, root.right, parent, child);
                assert false;
                }else{

                assert false;
                }
                assert false;
              } else if root.left == null && root.right != null {
                 parentsUniqueHelper(root, root.right, parent, child);
                assert false;
              } else if root.left != null && root.right == null {
                 parentsUniqueHelper(root, root.left, parent, child);
                assert false;

              } else {
                assert false;
              }
          //  parentsUniqueHelper(root, root, parent, child);
            }
          }
          assert false;
        }
      }
    }
}