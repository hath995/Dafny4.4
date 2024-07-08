module SOSqrt {
    function toOdd(n: nat): nat
        requires n > 0
    {
        2*n-1
    }

    function SumOfNOddNumbers(n: nat): nat {
        if n == 0 then 0 else toOdd(n)+SumOfNOddNumbers(n-1)
    }

    lemma SumOddIsSquared(n: nat)
        ensures SumOfNOddNumbers(n) == n*n
    {}

    lemma SquareOfGreatNLarger(root: nat, n: nat)
        requires n > root
        ensures SumOfNOddNumbers(n) > SumOfNOddNumbers(root)
    {}

    lemma lessSquared(a: nat, b: nat)
        requires a <= b
        ensures a*a <= b*b
    {
        if a == b {
            assert a*a <= b*b;
        }else{
            var diff := b-a; 
            assert diff > 0;
            calc {
                b*b;
                (a+diff)*(a+diff);
                a*a +2*a*diff + diff * diff;
            }
            assert a*a <= b*b;
        }
    }

    predicate IsNatSqrt(root: nat, n: nat) 
    {
        (n <= 1 && root * root == n) || (n > 1 && (root-1) * (root -1) < n && root * root >= n )
    }

    lemma ThereIsAMax(s: set<nat>)
    requires s != {}
    ensures exists x :: x in s && forall y :: y in s ==> x >= y
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
        ThereIsAMax(s');
    }
    }

    lemma  NatSqrtExist(n: nat) 
        ensures exists root: nat :: IsNatSqrt(root, n)
    {
        if n <= 1 {
            assert IsNatSqrt(n,n);
        }else{
            assert n > 1;
            var setOfLess := set k: nat | 0 < k < n && SumOfNOddNumbers(k) < n; 
            assert SumOfNOddNumbers(1) == 1;
            assert 1 in setOfLess;
            assert setOfLess != {};
            ThereIsAMax(setOfLess);
            var r :| r in setOfLess && forall y :: y in setOfLess ==> r >= y;
            assert SumOfNOddNumbers(r) < n;
            SumOddIsSquared(r);
            assert r*r < n;
            assert (r+1)*(r+1) >= n by {
                if (r+1)*(r+1) < n {
                    assert r+1 !in setOfLess;
                    assert false;
                }
            }
            assert IsNatSqrt(r+1, n);
        }
    }

    lemma sqrtRelation(s: nat, t: nat, i: nat, j: nat)
        requires 1 < s < t
        requires IsNatSqrt(i, s)
        requires IsNatSqrt(j, t)
        ensures i <= j
    {
        assert s > 1 && (i-1)*(i-1) < s && i*i >= s;
        assert t > 1 && (j-1)*(j-1) < t && j*j >= t;
        assert i <= j;
    }

    method sqrt(val :nat) returns (root:nat)
        ensures val == 0 ==> root == 0
        ensures val == 1 ==> root == 1
        ensures val != 0 ==> root * root >= val
        ensures val != 0 ==> (root - 1) * (root - 1) < val
        ensures val != 0 ==> forall n : nat :: n < root ==> n*n < val
        ensures IsNatSqrt(root, val)
    {
        root := 0;
        var est: int := val;
        while (est > 0)
            invariant val == 0 ==> root == 0
            invariant est == val - SumOfNOddNumbers(root)
            invariant root * root >= val - est
            invariant val > 1 ==> (root-1) * (root-1) < val
            invariant val == 1 ==> (root-1) * (root-1) <= val
            invariant est <= 0 ==> forall n :nat :: n > root ==> est > val - SumOfNOddNumbers(n)
            invariant est <= 0 ==> forall n: nat :: n < root ==> val - SumOfNOddNumbers(n) > 0
            decreases est
        {
            root := root + 1;
            ghost var oldEst := est;
            est := est - (2 * root - 1);

            assert val > 1 ==> (root-1) * (root-1) < val by {
                assert oldEst > 0;
                SumOddIsSquared(root-1);
            }
            assert est <= 0 ==> forall n :nat :: n > root ==> est > val-SumOfNOddNumbers(n) by {
                forall n | n > root 
                    ensures est > val-SumOfNOddNumbers(n)
                {
                    assert n >= root +1;
                    SquareOfGreatNLarger(root, n);
                }
            }
            assert est <= 0 ==> forall n :nat :: n < root ==> val-SumOfNOddNumbers(n) > 0 by {
                if est <= 0 {
                    assert val >= 1;
                    forall n : nat | n < root 
                        ensures val-SumOfNOddNumbers(n) > 0
                    {
                        SumOddIsSquared(n);
                        lessSquared(n, root-1);
                        assert n*n <= (root-1) * (root-1);
                    }
                }
            }
        }
    }
}
                    // assert val != 0 ==> (root-1) * (root-1) <= val by {
                    //     assert oldEst > 0;
                    //     SumOddIsSquared(root-1);
                    // }
    // invariant est == val ==> root == 0
    // if val == 0 {
            // // assert est == val-SumOfNOddNumbers(root);
            // // assert SumOfNOddNumbers(0) == 0;
            // // assert est == val;
            // // assert val == 0 ==> est == 0;
            // // assert val == 0 ==> root == 0;

            // }else{
            //     assert root * root >= val;
            //     assert (root-1) * (root-1) <= val;
            //     // assert est == val-SumOfNOddNumbers(root);
            // }
            // if val != 0 {
                // assert root * root >= val;
                // assert (root-1) * (root-1) <= val;
            // }

            // assert est == 0 ==> root * root == val by {
            //     SumOddIsSquared(root);
            // }
            // if val == 1 {
            //     assert root != 0;
            //     // assert est == 0;
            //     // // if root > 1 {
            //     // //     assert false;
            //     // // }
            //     assert root ==1;            }
//  assert est <= 0 ==> forall n :nat :: n < root ==> val-SumOfNOddNumbers(n) > 0 by {
//                         if est <= 0 {
//                             assert val >= 1;
//                             if val == 1 {
//                             // forall n : nat | n < root 
//                             //     ensures val-SumOfNOddNumbers(n) > 0
//                             // {
//                             //     assert n <= root - 1;
//                             //     SquareOfGreatNLarger(n, root);
//                             //     SumOddIsSquared(root);
//                             //     SumOddIsSquared(n);
//                             // }
//                             }else{
//                             forall n : nat | n < root 
//                                 ensures val-SumOfNOddNumbers(n) > 0
//                             {
//                                 SumOddIsSquared(n);
//                                 lessSquare(n, root-1);
//                                 assert n*n <= (root-1) * (root-1);
//                             }

//                             }
//                         }
//                     }
//   assert est <= 0 ==> forall n :nat :: n > root ==> est > val-SumOfNOddNumbers(n) by {
//                         forall n | n > root 
//                             ensures est > val-SumOfNOddNumbers(n)
//                         {
//                             // assert SumOfNOddNumbers(n+1) > SumOfNOddNumbers(n);
//                             assert n >= root +1;
//                             // assume SumOfNOddNumbers(n) > SumOfNOddNumbers(root);
//                             SquareOfGreatNLarger(root, n);
//                             // assert SumOfNOddNumbers(n) > SumOfNOddNumbers(root);
//                             // assert val-SumOfNOddNumbers(n) > val-SumOfNOddNumbers(n+1);
//                             // assert est == val-SumOfNOddNumbers(root);
//                         }
//                     }