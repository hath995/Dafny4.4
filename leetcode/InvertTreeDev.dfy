include "./invertTree.dfy"
module InvertTreeDev {
    import opened InvertBinaryTree 

    // lemma {:verify } {:vcs_split_on_every_assert} PreorderTraversalSubSlices2(root: TreeNode)
    //     requires root.Valid()
    //     ensures forall node :: node in root.repr ==> exists k :: 0<=k < |PreorderTraversal(root)| && PreorderTraversal(node) == PreorderTraversal(root)[k..|PreorderTraversal(node)|+k]
    //     decreases root.repr
    // {
    //     forall node | node in root.repr 
    //         ensures exists k :: 0<=k < |PreorderTraversal(root)| && PreorderTraversal(node) == PreorderTraversal(root)[k..|PreorderTraversal(node)|+k]
    //     {
    //         if node == root {
    //             assert PreorderTraversal(node) == PreorderTraversal(root)[0..|PreorderTraversal(root)|];

    //             assert exists k :: 0<=k < |PreorderTraversal(root)| && PreorderTraversal(node) == PreorderTraversal(root)[k..|PreorderTraversal(node)|+k];
    //             // assert exists k,j :: 0<=k<=j<= |PreorderTraversal(root)| && PreorderTraversal(node) == PreorderTraversal(root)[k..j];
    //         }else if node == root.left {
    //             if root.right == null {
    //                 assert PreorderTraversal(root) == [root]+PreorderTraversal(root.left);
    //                 assert PreorderTraversal(node) == PreorderTraversal(root)[1..|PreorderTraversal(root)|];
    //             }else{
    //                 assert PreorderTraversal(root) == [root]+PreorderTraversal(root.left)+PreorderTraversal(root.right);
    //                 assert |PreorderTraversal(root.left)| < |PreorderTraversal(root)|;
    //                 assert PreorderTraversal(node) == PreorderTraversal(root)[1..|PreorderTraversal(node)|+1];
    //                 childTraversalSize(root, node);
    //                 assert 0 <= 1 <= |PreorderTraversal(node)|+1 <= |PreorderTraversal(root)|;
    //             }
    //             assert exists k :: 0<=k < |PreorderTraversal(root)| && PreorderTraversal(node) == PreorderTraversal(root)[k..|PreorderTraversal(node)|+k];
    //             // assert exists k,j :: 0<=k<=j<= |PreorderTraversal(root)| && PreorderTraversal(node) == PreorderTraversal(root)[k..j];
    //         }else if node == root.right {
    //             if root.left == null {
    //                 assert PreorderTraversal(root) == [root]+PreorderTraversal(root.right);
    //                 assert PreorderTraversal(node) == PreorderTraversal(root)[1..|PreorderTraversal(root)|];
    //             }else{
    //                 assert PreorderTraversal(root) == [root]+PreorderTraversal(root.left)+PreorderTraversal(root.right);
    //                 childTraversalSize(root, node);
    //                 childTraversalSize(root, root.left);
    //                 // assert |PreorderTraversal(root.left)| < |PreorderTraversal(root)|;
    //                 // assert |PreorderTraversal(root.right)| < |PreorderTraversal(root)|;
    //                 assert PreorderTraversal(node) == PreorderTraversal(root)[(1+|PreorderTraversal(root.left)|)..|PreorderTraversal(root)|];
    //                 assert 0 <= 1+|PreorderTraversal(root.left)| <= |PreorderTraversal(root)|;
    //             }
    //             assert exists k :: 0<=k < |PreorderTraversal(root)| && PreorderTraversal(node) == PreorderTraversal(root)[k..|PreorderTraversal(node)|+k];
    //             // assert exists k,j :: 0<=k<=j<= |PreorderTraversal(root)| && PreorderTraversal(node) == PreorderTraversal(root)[k..j];
    //         }else if node != root && node != root.right && node != root.left {
    //             childInRootRepr(root, node);
    //             if root.right == null && root.left == null {
    //                 assert false;
    //             } else if root.right != null && root.left == null {
    //                 assert node in root.right.repr;
    //                 PreorderTraversalSubSlices2(root.right);
    //                 PreorderTraversalSlices(root.right);
    //                 childTraversalSize(root, root.right);
    //                 childTraversalSize(root, node);
    //                 childTraversalSize(root.right, node);
    //                 assert node in PreorderTraversal(root.right);
    //                 var x :| 0 <= x <  |PreorderTraversal(root.right)| && PreorderTraversal(node) == PreorderTraversal(root.right)[x..|PreorderTraversal(node)|+x];
    //                 assert PreorderTraversal(root)[1..|PreorderTraversal(root.right)|+1] == PreorderTraversal(root.right);
    //                 assert PreorderTraversal(root)[1+x..1+x+|PreorderTraversal(node)|] == PreorderTraversal(node);
    //                 assert 0 <= 1+x <= |PreorderTraversal(root)|;
    //                 assert exists k :: 0<=k < |PreorderTraversal(root)| && PreorderTraversal(node) == PreorderTraversal(root)[k..|PreorderTraversal(node)|+k];
    //             } else if root.right == null && root.left != null {
    //                 assert node in root.left.repr;
    //                 PreorderTraversalSubSlices2(root);
    //                 PreorderTraversalSlices(root.left);

    //                 childTraversalSize(root, root.left);
    //                 childTraversalSize(root, node);
    //                 childTraversalSize(root.left, node);
    //                 assert node in PreorderTraversal(root.left);
    //                 var x :| 0 <= x  < |PreorderTraversal(root.left)| && PreorderTraversal(node) == PreorderTraversal(root.left)[x..|PreorderTraversal(node)|+x];
    //                 assert PreorderTraversal(root)[1..|PreorderTraversal(root.left)|+1] == PreorderTraversal(root.left);
    //                 assert PreorderTraversal(root)[1+x..1+|PreorderTraversal(node)|+x] == PreorderTraversal(node);
    //                 assert 0 <= 1+x <= |PreorderTraversal(root)|;
    //                 assert exists k :: 0<=k < |PreorderTraversal(root)| && PreorderTraversal(node) == PreorderTraversal(root)[k..|PreorderTraversal(node)|+k];
    //             }else if root.right != null && root.right != null {
    //                 if node in root.right.repr {
    //                 PreorderTraversalSlices(root);
    //                 PreorderTraversalSubSlices2(root.right);
    //                 childTraversalSize(root, root.right);
    //                 childTraversalSize(root, node);
    //                 childTraversalSize(root.right, node);
    //                 assert node in PreorderTraversal(root.right);

    //                 var x :| 0 <= x < |PreorderTraversal(root.right)| && PreorderTraversal(node) == PreorderTraversal(root.right)[x..|PreorderTraversal(node)|+x];
    //                 assert PreorderTraversal(root)[|PreorderTraversal(root.left)|+1..] == PreorderTraversal(root.right);
    //                 assert PreorderTraversal(root)[|PreorderTraversal(root.left)|+x..|PreorderTraversal(root.left)|+|PreorderTraversal(node)|+x] == PreorderTraversal(node);
    //                 assert 0 <= |PreorderTraversal(root.left)|+x <= |PreorderTraversal(root.left)|+|PreorderTraversal(node)|+x <= |PreorderTraversal(root)|;
    //                 }else if node in root.left.repr {
    //                 PreorderTraversalSlices(root);
    //                 PreorderTraversalSubSlices2(root.left);
    //                 childTraversalSize(root, root.left);
    //                 childTraversalSize(root, node);
    //                 childTraversalSize(root.left, node);
    //                 assert node in PreorderTraversal(root.left);
    //                 var x :| 0 <= x < |PreorderTraversal(root.left)| && PreorderTraversal(node) == PreorderTraversal(root.left)[x..|PreorderTraversal(node)|+x];
    //                 assert PreorderTraversal(root)[1..|PreorderTraversal(root.left)|+1] == PreorderTraversal(root.left);
    //                 assert PreorderTraversal(root)[1+x..1+|PreorderTraversal(node)|+x] == PreorderTraversal(node);
    //                 assert 0 <= 1+x  <= |PreorderTraversal(root)|;

    //                 }
    //             }
    //             assert exists k :: 0<=k< |PreorderTraversal(root)| && PreorderTraversal(node) == PreorderTraversal(root)[k..|PreorderTraversal(node)|+k];
    //         }else{
    //             assert false;
    //         }
    //         // assert node != root && node != root.right && node != root.left;
    //             assert exists k :: 0<=k < |PreorderTraversal(root)| && PreorderTraversal(node) == PreorderTraversal(root)[k..|PreorderTraversal(node)|+k];
    //     }
    //     // assert forall node :: node in root.repr ==> exists k,j :: 0<=k<=j<= |PreorderTraversal(root)| && PreorderTraversal(node) == PreorderTraversal(root)[k..j];
    // }

 lemma sliceSlice<T>(xs: seq<T>, ys: seq<T>, zs: seq<T>, y: nat,  x: nat)
      requires |ys| > 0
      requires |xs| >= |ys|
      requires 0 < |zs|+x <= |ys|
      requires y < |xs|
      requires x < |ys|
      requires xs[y..] == ys
      requires ys[x..|zs|+x] == zs
      ensures xs[y+x..|zs|+x+y] == zs
   {
    assert xs[y..] == ys;
    assert xs[y..y+|ys|] == ys;
    assert ys[x..|zs|+x] == zs;
    assert xs[y+x..|zs|+x+y] == ys[x..|zs|+x];
   }

    lemma {:verify }  PreorderTraversalSubSlices2(root: TreeNode, node: TreeNode) returns (k: nat)
        requires root.Valid()
        requires node.Valid()
        requires node in root.repr
        ensures 0<=k < |PreorderTraversal(root)|
        ensures |PreorderTraversal(node)|+k <= |PreorderTraversal(root)| 
        ensures PreorderTraversal(node) == PreorderTraversal(root)[k..|PreorderTraversal(node)|+k]
        decreases root.repr
    {
        if node == root {
            // assert PreorderTraversal(node) == PreorderTraversal(root)[0..|PreorderTraversal(root)|];

            // assert 0<=0 < |PreorderTraversal(root)|;
            // assert |PreorderTraversal(node)|+0 <= |PreorderTraversal(root)|;
            // assert PreorderTraversal(node) == PreorderTraversal(root)[0..|PreorderTraversal(node)|+0];
            // assert 0 < |PreorderTraversal(root)| && PreorderTraversal(node) == PreorderTraversal(root)[0..|PreorderTraversal(node)|+0];
            return 0;
            // assert exists k,j :: 0<=k<=j<= |PreorderTraversal(root)| && PreorderTraversal(node) == PreorderTraversal(root)[k..j];
        }else if node == root.left {
            if root.right == null {
                assert PreorderTraversal(root) == [root]+PreorderTraversal(root.left);
                // assert PreorderTraversal(node) == PreorderTraversal(root)[1..|PreorderTraversal(node)|+1];
                // assert 1 < |PreorderTraversal(root)|;
                // assert |PreorderTraversal(node)|+1 <= |PreorderTraversal(root)|;
                assert PreorderTraversal(node) == PreorderTraversal(root)[1..|PreorderTraversal(node)|+1];
                return 1;
            }else{
                assert PreorderTraversal(root) == [root]+PreorderTraversal(root.left)+PreorderTraversal(root.right);
                // assert |PreorderTraversal(root.left)| < |PreorderTraversal(root)|;
                // assert PreorderTraversal(node) == PreorderTraversal(root)[1..|PreorderTraversal(node)|+1];
                // childTraversalSize(root, node);
                // assert 0 <= 1 <= |PreorderTraversal(node)|+1 <= |PreorderTraversal(root)|;
                // assert 1 < |PreorderTraversal(root)|;
                // assert |PreorderTraversal(node)|+1 <= |PreorderTraversal(root)|;
                // assert PreorderTraversal(node) == PreorderTraversal(root)[1..|PreorderTraversal(node)|+1];
                return 1;
            }
            // assert exists k,j :: 0<=k<=j<= |PreorderTraversal(root)| && PreorderTraversal(node) == PreorderTraversal(root)[k..j];
        }else if node == root.right {
            if root.left == null {
                assert PreorderTraversal(root) == [root]+PreorderTraversal(root.right);
                assert PreorderTraversal(node) == PreorderTraversal(root)[1..|PreorderTraversal(root.right)|+1];
                // assert 1 < |PreorderTraversal(root)|;
                // assert |PreorderTraversal(node)|+1 <= |PreorderTraversal(root)|;
                // assert PreorderTraversal(node) == PreorderTraversal(root)[1..|PreorderTraversal(node)|+1];
                return 1;
            }else{
                assert PreorderTraversal(root) == [root]+PreorderTraversal(root.left)+PreorderTraversal(root.right);
                // childTraversalSize(root, node);
                // childTraversalSize(root, root.left);
                // assert |PreorderTraversal(root.left)| < |PreorderTraversal(root)|;
                // assert |PreorderTraversal(root.right)| < |PreorderTraversal(root)|;
                assert PreorderTraversal(node) == PreorderTraversal(root)[(1+|PreorderTraversal(root.left)|)..|PreorderTraversal(root.left)|+|PreorderTraversal(root.right)|+1];
                assert 0 <= 1+|PreorderTraversal(root.left)| < |PreorderTraversal(root)|;
                // assert PreorderTraversal(node) == PreorderTraversal(root)[1+|PreorderTraversal(root.left)|..|PreorderTraversal(node)|+|PreorderTraversal(root.left)|+1];
                // assert 1+|PreorderTraversal(root.left)| < |PreorderTraversal(root)|;
                // assert |PreorderTraversal(node)|+1+|PreorderTraversal(root.left)| <= |PreorderTraversal(root)|;
                // assert PreorderTraversal(node) == PreorderTraversal(root)[1+|PreorderTraversal(root.left)|..|PreorderTraversal(node)|+1+|PreorderTraversal(root.left)|];
                return 1+|PreorderTraversal(root.left)|;
            }
            // assert exists k,j :: 0<=k<=j<= |PreorderTraversal(root)| && PreorderTraversal(node) == PreorderTraversal(root)[k..j];
        }else if node != root && node != root.right && node != root.left {
            childInRootRepr(root, node);
            if root.right == null && root.left == null {
                assert false;
            } else if root.right != null && root.left == null {
                assert node in root.right.repr;
                assert root.right.Valid();
                PreorderTraversalSlices(root.right);
                // childTraversalSize(root, root.right);
                // childTraversalSize(root, node);
                // childTraversalSize(root.right, node);
                var x := PreorderTraversalSubSlices2(root.right, node);
                sliceSlice(PreorderTraversal(root), PreorderTraversal(root.right), PreorderTraversal(node), 1, x);
                // assert node in PreorderTraversal(root.right);
                // var x :| 0 <= x <  |PreorderTraversal(root.right)| && PreorderTraversal(node) == PreorderTraversal(root.right)[x..|PreorderTraversal(node)|+x];
                // assert PreorderTraversal(root)[1..|PreorderTraversal(root.right)|+1] == PreorderTraversal(root.right);
                assert PreorderTraversal(root)[1+x..|PreorderTraversal(node)|+1+x] == PreorderTraversal(node);
                assert 1+x < |PreorderTraversal(root)|;
                assert |PreorderTraversal(node)|+1+x <= |PreorderTraversal(root)|;
                // assert PreorderTraversal(node) == PreorderTraversal(root)[1+x..|PreorderTraversal(node)|+1+x];
                // assert 0 <= 1+x <= |PreorderTraversal(root)|;
                // assert exists k :: 0<=k < |PreorderTraversal(root)| && PreorderTraversal(node) == PreorderTraversal(root)[k..|PreorderTraversal(node)|+k];
                return 1+x;
            } else if root.right == null && root.left != null {
                assert node in root.left.repr;
                assert root.left.Valid();
                PreorderTraversalSlices(root.left);

                // childTraversalSize(root, root.left);
                // childTraversalSize(root, node);
                // childTraversalSize(root.left, node);
                var x:= PreorderTraversalSubSlices2(root.left, node);
                sliceSlice(PreorderTraversal(root), PreorderTraversal(root.left), PreorderTraversal(node), 1, x);
                // assert node in PreorderTraversal(root.left);
                // var x :| 0 <= x  < |PreorderTraversal(root.left)| && PreorderTraversal(node) == PreorderTraversal(root.left)[x..|PreorderTraversal(node)|+x];
                // assert PreorderTraversal(root)[1..|PreorderTraversal(root.left)|+1] == PreorderTraversal(root.left);
                assert PreorderTraversal(root)[1+x..1+|PreorderTraversal(node)|+x] == PreorderTraversal(node);
                // assert 0 <= 1+x <= |PreorderTraversal(root)|;
                assert |PreorderTraversal(node)|+1+x <= |PreorderTraversal(root)|;
                // assert PreorderTraversal(node) == PreorderTraversal(root)[1+x..|PreorderTraversal(node)|+1+x];
                assert 0 <= 1+x < |PreorderTraversal(root)|;
                // assert exists k :: 0<=k < |PreorderTraversal(root)| && PreorderTraversal(node) == PreorderTraversal(root)[k..|PreorderTraversal(node)|+k];
                return 1+x;
            }else if root.right != null && root.right != null {
                assert PreorderTraversal(root) == [root]+PreorderTraversal(root.left)+PreorderTraversal(root.right);
                assert |PreorderTraversal(root)| == 1+ |PreorderTraversal(root.left)|+|PreorderTraversal(root.right)|;
                if node in root.right.repr {
                    PreorderTraversalSlices(root);
                    assert root.right.Valid();
                    var x := PreorderTraversalSubSlices2(root.right, node);
                    // childTraversalSize(root, root.right);
                    // childTraversalSize(root, node);
                    // childTraversalSize(root.right, node);
                    // traversalSize(root);
                    // traversalSize(root.right);
                    // traversalSize(root.left);
                    // traversalSize(node);
                    assert PreorderTraversal(node) == PreorderTraversal(root.right)[x..|PreorderTraversal(node)|+x];
                    // assert |PreorderTraversal(root.right)| > 0;
                    // assert |PreorderTraversal(root.left)| > 0;
                    // assert |PreorderTraversal(node)| > 0;
                    // assert node !in root.left.repr;
                    // assert node !in PreorderTraversal(root.left);
                    // assert node in PreorderTraversal(root.right);
                    // assert 0 <= x < |PreorderTraversal(root.right)|;
                    // assert |PreorderTraversal(node)|+x <= |PreorderTraversal(root.right)|;
                    // assert |PreorderTraversal(root.left)|+1 < |PreorderTraversal(root)|;
                    // assert |PreorderTraversal(root.left)|+1+|PreorderTraversal(node)|+x <= |PreorderTraversal(root)|;
                    // assert PreorderTraversal(root)[0..1] == [root];
                    // assert PreorderTraversal(root)[1..|PreorderTraversal(root.left)|+1] == PreorderTraversal(root.left);
                    // assert PreorderTraversal(root)[|PreorderTraversal(root.left)|+1..] == PreorderTraversal(root.right);
                    // assert PreorderTraversal(root)[|PreorderTraversal(root.left)|+1..|PreorderTraversal(root.left)|+1+|PreorderTraversal(root.right)|] == PreorderTraversal(root)[|PreorderTraversal(root.left)|+1..];
                    // assert PreorderTraversal(root)[|PreorderTraversal(root.left)|+1..|PreorderTraversal(root.left)|+1+|PreorderTraversal(root.right)|] == PreorderTraversal(root.right);
                    // var a := PreorderTraversal(root)[|PreorderTraversal(root.left)|+1..];
                    // var b := PreorderTraversal(root)[|PreorderTraversal(root.left)|+1..|PreorderTraversal(root.left)|+1+|PreorderTraversal(root.right)|];
                    // assert a == b;
                    // assert a == PreorderTraversal(root.right);
                    var y := |PreorderTraversal(root.left)|+1;
                    // assert 0 <= y < |PreorderTraversal(root)|;
                    assert 0 <= y+x < |PreorderTraversal(root)|;
                    assert y+x+|PreorderTraversal(node)| <= |PreorderTraversal(root)|;
                    sliceSlice(PreorderTraversal(root), PreorderTraversal(root.right), PreorderTraversal(node), y, x);
                    // assert PreorderTraversal(root)[y..] == PreorderTraversal(root.right);
                    // assert PreorderTraversal(root)[y..][x..|PreorderTraversal(node)|+x] == PreorderTraversal(node);
                    // assert a[x..|PreorderTraversal(node)|+x] == PreorderTraversal(node);
                    // assert b[x..|PreorderTraversal(node)|+x] == PreorderTraversal(node);
                    // assert PreorderTraversal(root)[y+x..|PreorderTraversal(node)|+y+x] == PreorderTraversal(node);
                    // assert PreorderTraversal(root)[|PreorderTraversal(root.left)|+1+x..|PreorderTraversal(root.left)|+1+|PreorderTraversal(node)|+x] == PreorderTraversal(node);
                    // assert 0 <= |PreorderTraversal(root.left)|+x <= |PreorderTraversal(root.left)|+|PreorderTraversal(node)|+x <= |PreorderTraversal(root)|;
                    return y+x;
                }else if node in root.left.repr {
                    PreorderTraversalSlices(root);
                    assert root.left.Valid();
                    var x:= PreorderTraversalSubSlices2(root.left, node);
                    // sliceSlice(PreorderTraversal(root), PreorderTraversal(root.left), PreorderTraversal(node), 1, x);
                    // childTraversalSize(root, root.left);
                    // childTraversalSize(root, node);
                    // childTraversalSize(root.left, node);
                    // assert node in PreorderTraversal(root.left);
                    assert 0 <= x < |PreorderTraversal(root.left)|;
                    // assert x+|PreorderTraversal(node)| <= |PreorderTraversal(root.left)|;
                    assert x+1 < |PreorderTraversal(root)|;
                    // assert 1+|PreorderTraversal(node)|+x <= |PreorderTraversal(root.left)|+1;
                    assert 1 <= 1+x;
                    assert PreorderTraversal(node) == PreorderTraversal(root.left)[x..|PreorderTraversal(node)|+x];
                    // assert PreorderTraversal(root)[1..|PreorderTraversal(root.left)|+1] == PreorderTraversal(root.left);
                    assert PreorderTraversal(root)[1+x..1+|PreorderTraversal(node)|+x] == PreorderTraversal(node);
                    // assert 0 <= 1+x  <= |PreorderTraversal(root)|;
                    assert |PreorderTraversal(node)|+1+x <= |PreorderTraversal(root)|;
                    // assert PreorderTraversal(node) == PreorderTraversal(root)[1+x..|PreorderTraversal(node)|+1+x];
                    // assert 0 <= 1+x < |PreorderTraversal(root)|;
                    return 1+x;
                }else{
                    assert false;
                }
            }else{
                assert false;
            }
        }else{
            assert false;
        }
    }
}