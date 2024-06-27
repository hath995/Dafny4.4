include "./invertTree.dfy"
include "./preorderTraversalDefs.dfy"
module PreorderTraversal {
    import opened InvertBinaryTree
    import Std.Collections.Seq
    import opened PreorderTraversalSupp

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
      requires allLeftVisited(parents, visited)
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

    lemma {:verify false} {:vcs_split_on_every_assert} FlatMapVisitedARN(stack: seq<TreeNode>, parents: seq<TreeNode>, visited: set<TreeNode>, unvisited: set<TreeNode>, current: TreeNode, newStack: seq<TreeNode>, newParents: seq<TreeNode>)
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
      assume {:axiom} newParents == [];
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
              assert somex in allRightPlusChildren(parents, visited);
              var parentofx :| 0 <= parentofx < |parents| && somex in children(parents[parentofx]);
              assert somex in visited;
              assert false;
            }
          }
        }
        assert stack[..|stack|-1]+childStack(stack[|stack|-1]) == [];
      }
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

      Why this might be useful is that when we wind back to a previous parent then we are basically working
      our way back up the function call stack and now let k be the new last unfinished parent then
      parent[k].left != null && parent[k].right != null ==> result[parentIndices[k]+1..i+1] == PreorderTraversal(parent[k].left)+PreorderTraversal(parent[k].right) or 
      parent[k].left != null && parent[k].right == null ==> result[parentIndices[k]+1..i+1] == PreorderTraversal(parent[k].left) or
      parent[k].left == null && parent[k].right != null ==> result[parentIndices[k]+1..i+1] == PreorderTraversal(parent[k].right) or 

      we can also check if
      i - parentIndices[k]+1 == parent[k].left.TreeSize() + parent[k].right.TreeSize()
      i - parentIndices[k]+1 == parent[k].left.TreeSize()
      i - parentIndices[k]+1 == parent[k].right.TreeSize()
      respectively 
      if parentIndices[k] == 0 and i == |root.TreeSize()| then we are done in theory.
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
            invariant parents != [] ==> stack != []

            invariant parents != [] ==> childOf(stack[ |stack| -1], parents[ |parents| -1])
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
            // parentsEmptyImplyStackEmpty(parents, stack, visited, unvisited);
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

    lemma setTest<T>(test: set<T>)
      requires test == {}
    {
      assert test <= test;
    }

    ghost predicate allValidParents(root: TreeNode, node: TreeNode) 
      reads root, root.repr, root.parentRepr, root.parent, node, node.repr, node.parentRepr, node.parent
      requires root.Valid()
      requires root.ParentValid()
      requires node.Valid()
      requires node.ParentValid()
    {
      // (root.parent == null) && forall x :: x in root.repr ==> x.parentRepr < root.repr && x.ParentValid() && (root != x ==> x.parent != null)
      // forall x :: x in root.repr ==> x.parentRepr < root.repr+{root.parent} && x.ParentValid() && (root != x ==> x.parent != null)
      forall x :: x in node.repr ==> x.parentRepr <= root.repr-x.repr && x.ParentValid() && (root != x ==> x.parent != null)
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
      // forall x | x in child.repr 
      //  ensures x.parentRepr <= child.repr-x.repr && x.ParentValid() && (child != x ==> x.parent != null)
      //  {
      //   assert x in root.repr;
      //   // assert x.parentRepr < root.repr+{root.parent} && x.ParentValid() && (root != x ==> x.parent != null);
      //   assert x != root by {
      //     if root.right == null && root.left == null {
      //       assert false;
      //     } else if root.right == null && root.left != null {
      //       ChildNodesAreValid(root.left, child);
      //       ChildNodesAreValid(child, x);
      //       assert x in root.left.repr;
      //     } else if root.right != null && root.left == null {
      //       ChildNodesAreValid(root.right, child);
      //       ChildNodesAreValid(child, x);
      //       assert x in root.right.repr;
      //     } else if root.right != null && root.left != null {
      //       if child in root.right.repr {
      //         ChildNodesAreValid(root.right, child);
      //         ChildNodesAreValid(child, x);
      //         assert x in child.repr;
      //         assert child.repr <= root.right.repr;
      //         assert x in root.right.repr;

      //       }else if child in root.left.repr {
      //         ChildNodesAreValid(root.left, child);
      //         ChildNodesAreValid(child, x);
      //         assert x in root.left.repr;
      //       }
      //     }
      //   }
      // assert x.parentRepr <= child.repr-x.repr; //Either need to fix definition of parentValid or AllValidParentsChild
      // assert x.ParentValid();
      // assert x != child ==> x.parent != null by {
      //     if x != child {
      //     assert x != child;
      //     assert x != root;
      //     assert x in root.repr;
      //     assert x.parent != null;
      //     }
      //   }

        // assert x.parentRepr < child.repr+{child.parent} && x.ParentValid() && (child != x ==> x.parent != null);
      //  }

    }

    lemma {:verify false} {:vcs_split_on_every_assert} parentsUniqueHelper(root: TreeNode, someNode: TreeNode,  parent: TreeNode, child: TreeNode)
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
      // childInRootRepr(root, parent);
      // childInRootRepr(root, child.parent);
     
        // childInRootRepr(someNode, child);
        childInRootRepr(someNode, child.parent);
        if parent != someNode && child.parent != someNode {
          //if child.parent in someNode.left && parent in someNode.right --> contradiction
          //if child.parent in someNode.right && parent in someNode.left --> contradiction
          //if child.parent in someNode.right && parent in someNode.right --> recursive call
          //if child.parent in someNode.left && parent in someNode.left --> recursive call
          //otherwise contradiction

        }else if parent != someNode && child.parent == someNode {
          childInRootRepr(someNode, parent);
          //if child.parent.right == child and parent in child.parent.left --> contradiction by !!
          //if child.parent.right == child and child.parent.left == null --> contradiction by parentValid()
          //if child.parent.right == child and parent in child.parent.right -> contradiction by ParenValid() 
          //if child.parent.left == child and parent in child.parent.right --> contradiction by !!
          //if child.parent.left == child and child.parent.right == null -> contradiction by ParenValid() 
          //if child.parent.left == child and parent in child.parent.left -> contradiction by ParenValid() 

          assert false;
        }else if parent == someNode && child.parent != someNode {
          //either parent.right == child || parent.left == child
          //if parent.right == child and child.parent in parent.left --> contradiction by !!
          //if parent.right == child and child.parent in parent.right -> contradiction by ParenValid() 
          //if parent.left == child and child.parent in parent.right --> contradiction by !!
          //if parent.left == child and child.parent in parent.left -> contradiction by ParenValid() 
          assert false;
        }else{
          assert parent == someNode && child.parent == someNode;
          assert false;
        }
        assert false;
      // if root.left == null && root.right == null {
      //   assert false;
      // }else if root.left != null && root.right != null {
      //   assert child in parent.repr;
      //   assert child in child.parent.repr;
      //   if child.parent in root.left.repr && parent in root.right.repr {
      //     ChildNodesAreValid(root.left, child.parent);
      //     ChildNodesAreValid(root.right, parent);
      //     assert child in root.left.repr;
      //     assert child in root.right.repr;
      //   assert false;
      //   }else if child.parent in root.right.repr && parent in root.left.repr {
      //     ChildNodesAreValid(root.left, parent);
      //     ChildNodesAreValid(root.right,child.parent);
      //     assert child in root.left.repr;
      //     assert child in root.right.repr;
      //   assert false;
      //   }else if child.parent in root.right.repr && parent in root.right.repr {
      //     ChildNodesAreValid(root.right,child.parent);
      //     assert child in root.right.repr;
      //     ChildNodesAreValid(root, root.right);
      //     // parentsUnique(root.right);
      //     if parent == root.right {
      //       parentsUniqueHelperRoot(root.right, parent, child);
      //     }else{
      //     parentsUniqueHelper(root, root.right, parent, child);
      //   }
      //   assert false;
      //   }else if child.parent in root.left.repr && parent in root.left.repr {
      //     ChildNodesAreValid(root.left,child.parent);
      //     assert child in root.left.repr;
      //     // parentsUnique(root.left);
      //     ChildNodesAreValid(root, root.left);
      //     parentsUniqueHelper(root, root.left, parent, child);
      //   assert false;
      //   }

      //   assert false;
      // }else if root.left == null && root.right != null {
      //   assert child.parent in root.right.repr;
      //   ChildNodesAreValid(root.right, child.parent);
      //   assert child in root.right.repr;
      //   assert parent in root.right.repr;
      //     // parentsUnique(root.right);
      //     ChildNodesAreValid(root, root.right);
      //     parentsUniqueHelper(root, root.right, parent, child);
      //   assert false;
      // }else if root.left != null && root.right == null {
      //   assert child.parent in root.left.repr;
      //   ChildNodesAreValid(root.left, child.parent);
      //   assert child in root.left.repr;
      //   assert parent in root.left.repr;
      //     // parentsUnique(root.left);
      //     ChildNodesAreValid(root, root.left);
      //     parentsUniqueHelper(root, root.left, parent, child);
      //   assert false;
      // }
        
      // assert false;
    }

    lemma {:verify } parentsUniqueHelperRoot(root: TreeNode, parent: TreeNode, child: TreeNode)
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
    
    lemma {:verify false}  parentsUnique(root: TreeNode)
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
          // ChildNodesAreValid(root, parent);
          // ChildNodesAreValid(root, child);
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
            // ChildNodesReprAreLess(root, child.parent);
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
           parentsUniqueHelper(root, root, parent, child);
            }
          }
          assert false;
        }
      }
    }


    /*
        By hitting F5 Dafny will attempt to run code in a Main method. You will need to add --standard-libraries to
        the run command to execute because of the imported flatten and map functions.

        This is very useful to test invariants.
        "expect" statements are the run time dual of "assert" statements. As in asserts task the verifier must test to be 
        true. Where as "expect" statements must be tested to be true during runtime.
    */
    method {:verify false} Main() 
    {
        var u := new TreeNode(20, null, null);
        var v := new TreeNode(21, null, null);
        var l := new TreeNode(12, u, v);
        // assert l.parentRepr == {};
        u.setParent(l);
        // assert l.right == v;
        v.setParent(l);
        var m := new TreeNode(13, null, null);
        var h := new TreeNode(8, l, m);
        m.setParent(h);
        l.setParent(h);
        var o := new TreeNode(14, null, null);
        var p := new TreeNode(15, null, null);
        var i := new TreeNode(9, o, p);
        o.setParent(i);
        p.setParent(i);
        var d := new TreeNode(4, h, i);
        h.setParent(d);
        i.setParent(d);
        var e := new TreeNode(5, null, null);
        var b := new TreeNode(2, d, e);
        d.setParent(b);
        e.setParent(b);
        var c := new TreeNode(3, null, null);
        var a := new TreeNode(1, b, c);
        b.setParent(a);
        c.setParent(a);
        assert c.ParentValid();
        var flat := Traverse(a);
        print mapNodes(flat), "\n";
        print mapNodes(PreorderTraversal(a)), "\n";

    }
}
