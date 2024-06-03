module Math {
    //imported from https://github.com/dafny-lang/dafny/blob/master/Test/dafny4/gcd.dfy
    type pos = x: nat | 1 <= x witness 1
    ghost predicate IsFactor(p: pos, x: pos) {
        exists q: pos ::  p * q == x
    }

    ghost function Factors(x: pos): set<pos> {
        set p: pos | p <= x  && IsFactor(p, x)  // error: set constructed must be finite
    }

    lemma FactorIsFactorOfLinearCombination(a: pos, b: pos, c: pos)
        requires IsFactor(a, b)
        requires IsFactor(a, c)
        ensures forall x,y :: linearCombination(b,x,c,y) > 0 ==> IsFactor(a, linearCombination(b,x,c,y))
    {
       forall x,y | linearCombination(b,x,c,y) > 0 
            ensures IsFactor(a, linearCombination(b,x,c,y))
       {
            var qq :| a*qq == c;
            var ll :| a*ll == b;
            calc {
                linearCombination(b,x,c,y);
                linearCombination(a*ll,x,a*qq,y);
                prod(a*ll,x) + prod(a*qq,y);
                == {reveal prod();}
                prod(prod(a,ll),x) + prod(prod(a,qq),y);
                == {prodAssociative(a,ll,x);}
                prod(a, prod(ll,x)) + prod(prod(a,qq),y);
                == {prodAssociative(a,qq,y);}
                prod(a, prod(ll,x)) + prod(a,prod(qq,y));
                == {prodDistributes(a, prod(ll,x), prod(qq,y));}
                prod(a, prod(ll,x) +prod(qq,y));
                == {reveal prod();}
                a * (ll*x + qq*y);
            }
            assert (ll*x + qq*y) > 0;
            assert a * (ll*x + qq*y) == linearCombination(b,x,c,y);
            assert IsFactor(a, linearCombination(b,x,c,y));

       } 
    }

    lemma FactorsHasAllFactors(x: pos)
        ensures forall n :: n in Factors(x) <==> n in iset p: pos | IsFactor(p, x)
    {
    }

    lemma FactorsContains1(x: pos)
        ensures 1 in Factors(x)
    {
        assert 1 * x == x;
    }

    lemma FactorsContainsSelf(x: pos)
        ensures x in Factors(x)
    {
        assert x * 1 == x;
    }

    ghost function Max(s: set<pos>): pos
        requires s != {}
    {
        MaxExists(s);
        var x :| x in s && forall y :: y in s ==> y <= x;
        x
    }
    lemma MaxExists(s: set<pos>)
        requires s != {}
        ensures exists x :: x in s && forall y :: y in s ==> y <= x
    {
        var x := FindMax(s);
    }

    ghost function FindMax(s: set<pos>): (max: pos)
        requires s != {}
        ensures max in s && forall y :: y in s ==> y <= max
    {
        var x :| x in s;
        if s == {x} then
            x
        else
            var s' := s - {x};
            assert s == s' + {x};
            var y := FindMax(s');
            if x < y then y else x
    }

    ghost function Min(s: set<pos>): pos 
        requires s != {}
        ensures forall x | x in s :: Min(s) in s && Min(s) <= x
    {
        var x :| x in s;
        if s == {x} then
            x
        else
            var y := Min(s - {x});
            assert s == (s-{x}) + {x};
            assert forall z | z in s :: z == x || (z in (s - {x}) && y <= z);
            if x < y then x else y
    }

    lemma WellOrderingPrinciple(s: iset<pos>)
        requires s != iset{}
        ensures exists min :: min in s && forall x | x in s && x != min :: min < x; 

    ghost function iMin(s: iset<pos>): pos
        requires s != iset{}
        ensures forall x | x in s && x != iMin(s) :: iMin(s) in s ==> iMin(s) < x
    {
        WellOrderingPrinciple(s);
        var min :| min in s && forall x | x in s && x != min :: min < x; 
        min
    }


    ghost function Gcd(x: pos, y: pos): pos {
        var common := Factors(x) * Factors(y);
        assert 1 in common by {
            FactorsContains1(x);
            FactorsContains1(y);
        }
        Max(common)
    }

    lemma AboutGcd(x: pos, y: pos)
        ensures IsFactor(Gcd(x, y), x)
        ensures IsFactor(Gcd(x, y), y)
        ensures forall p: pos :: IsFactor(p, x) && IsFactor(p, y) ==> p <= Gcd(x, y)
    {
        forall p: pos | IsFactor(p, x) && IsFactor(p, y)
            ensures p <= Gcd(x, y)
        {
            assert p in Factors(x) * Factors(y);
        }
    }

    lemma GcdSymmetric(x: pos, y: pos)
        ensures Gcd(x, y) == Gcd(y, x)
    {
        assert Factors(x) * Factors(y) == Factors(y) * Factors(x);
    }

    lemma GcdIdempotent(x: pos)
        ensures Gcd(x, x) == x
    {
        FactorsContainsSelf(x);
        assert x in Factors(x) * Factors(x);
    }

    lemma GcdSubtract(x: pos, y: pos)
        requires x < y
        ensures Gcd(x, y) == Gcd(x, y - x)
    {
        var p := Gcd(x, y);

        // By the definition of `Gcd`, we know that p is a factor of both x and y,
        // We now show that p is also a factor of y - x.
        assert IsFactor(p, y - x) by {
            var a :| p * a == x;
            var b :| p * b == y;
            calc {
            y - x;
            ==
            p * b - p * a;
            ==
            p * (b - a);
            }
        }

        // Hence, p is a common factor of x and y - x
        var common := Factors(x) * Factors(y - x);
        assert p in common;

        // It remains to show that, among the common factors of x and
        // y - x, p is the greatest
        forall q | q in common
            ensures q <= p
        {
            // q is a factor of both x and y - x, so a and b exist:
            var a :| q * a == x;
            var b :| q * b == y - x;
            assert IsFactor(q, y) by {
            calc {
                y;
            ==
                x + (y - x);
            ==
                q * a + q * b;
            ==
                q * (a + b);
            }
            }
            // We just showed that q is a common factor of x and y.
            assert q in Factors(x) * Factors(y);
            // By the definition of Gcd(x, y), we then have that q <= p.
        }
    }

    method EuclidGcd(X: pos, Y: pos) returns (gcd: pos)
        ensures gcd == Gcd(X, Y)
    {
        var x: pos, y: pos := X, Y;
        while
            invariant Gcd(x, y) == Gcd(X, Y)
            decreases x + y
        {
            case x < y =>
            GcdSubtract(x, y);
            y := y - x;
            case y < x =>
            calc {
                Gcd(x, y);
            ==  { GcdSymmetric(x, y); }
                Gcd(y, x);
            ==  { GcdSubtract(y, x); }
                Gcd(y, x - y);
            ==  { GcdSymmetric(y, x - y); }
                Gcd(x - y, y);
            }
            x := x - y;
        }
        GcdIdempotent(x);
        return x;
    }

    function linearCombination(a: int, x: int, b: int, y: int): int {
        // a*x + b*y
        prod(a,x) + prod(b,y)
    }

    function combinationSet(a: pos, b: pos): set<pos> 
    {
        // set x: nat,y: nat | 0 <= x <= a && 0 <= y <= b && a*x+b*y > 0 :: a*x+b*y
        set x: int,y: int | 0 <= x <= a && 0 <= y <= b && linearCombination(a,x,b,y) > 0 :: linearCombination(a,x,b,y)
    }

    ghost function icombinationSet(a: pos, b: pos): iset<pos> 
    {
        iset x: int,y: int | linearCombination(a,x,b,y) > 0 :: linearCombination(a,x,b,y)
        // iset x: int,y: int | a*x+b*y > 0 :: a*x+b*y
    }

    function {:opaque} prod(x: int, y: int): int {
        x * y
    }

    function divAdd(b: int, a: int, c: int): int {
        prod(b,a) + c
    }

    lemma {:verify true} DivisionAlgorithm(a: pos, b: pos)
        requires a != 0
        ensures exists q: nat,r:nat :: b == divAdd(q,a,r) && 0 <= r < a
    {
        var r := b%a;
        var q := b/a;
        reveal prod();
        assert b == divAdd(q,a,r);
    }

    lemma prodAssociative(a: int, b: int, c: int)
        ensures prod(prod(a,b),c) == prod(a, prod(b,c))
    {
        reveal prod();
    }

    lemma prodCommutes(a: int, b: int)
        ensures prod(a,b) == prod(b,a)
    {
        reveal prod();
    }

    lemma prodCommutesThree(a: int, b: int, c: int) 
        ensures prod(a, prod(b, c)) == prod(b, prod(a, c))
    {
        reveal prod();
    }

    lemma prodDistributes(a: int, b: int, c: int)
        ensures prod(a, b + c) == prod(a,b) + prod(a,c)
    {
        reveal prod();
    }

    lemma prodDistributesMinus(a: int, b: int, c: int)
        ensures prod(a, b - c) == prod(a,b) - prod(a,c)
    {
        reveal prod();
    }

    lemma prodIdentity(a: int)
        ensures a == prod(a, 1)
        ensures a == prod(1, a)
    {
        reveal prod();
    }
    lemma prodNegative(a: int, b: int)
        ensures -prod(a,b) == prod(-1, prod(a,b))
    {
        reveal prod();
    }

    lemma linearCombinationOfPosisPos(a: pos, b: pos)
        ensures linearCombination(a,a,b,b) > 0
    {
        assert a > 0;
        assert b > 0;
        calc {
            linearCombination(a,a,b,b);
            prod(a,a) + prod(b,b);
            == {reveal prod();}
            a*a + b * b;
        }
    }
    
    lemma DivAddZero(a: int, q: int, d: int)
        requires a > 0
        requires d > 0
        requires a == divAdd(q,d,0)
        ensures IsFactor(d,a)
    {
        reveal prod();
        calc {
            divAdd(q,d, 0);
            prod(q,d)  + 0;
            prod(q,d);
            q*d;
            a;
        }
        assert d*q == a;
        assert IsFactor(d,a);
    }
    
    lemma GcdLinearCombination(a: pos, b: pos)
        ensures exists x,y :: Gcd(a,b) == linearCombination(a,x,b,y)
    {
        AboutGcd(a,b);
        var S := icombinationSet(a,b);
        linearCombinationOfPosisPos(a,b);
        assert linearCombination(a,a,b,b) > 0 && linearCombination(a,a,b,b) in S;
        var d := iMin(S);
        assert d in S;
        var s,t :| d == linearCombination(a,s,b,t);
        DivisionAlgorithm(d,a);
        var q,r :| a == divAdd(q,d,r) &&  0 <= r < d;
        if r > 0 {
            calc {
                r;
                a - prod(q,d);
                a - prod(q, linearCombination(a,s,b,t));
                a - prod(q, prod(a,s)+prod(b,t));
                == {prodDistributes(q, prod(a,s), prod(b,t));}
                a - (prod(q, prod(a,s))+prod(q, prod(b,t)));
                == {prodCommutesThree(q,a,s);}
                a - (prod(a, prod(q,s))+prod(q, prod(b,t)));
                == {prodCommutesThree(q,b,t);}
                a - prod(a, prod(q,s)) - prod(b, prod(q,t));
                =={ prodIdentity(a);}
                prod(a,1) - prod(a, prod(q,s)) - prod(b, prod(q,t));
                == { prodDistributesMinus(a, 1, prod(q,s));}
                prod(a,1 - prod(q,s)) - prod(b, prod(q,t));
                prod(a,1 - prod(q,s)) - prod(b, prod(q,t));
                == {prodNegative(b, prod(q,t));}
                prod(a,1 - prod(q,s)) + prod(-1,prod(b, prod(q,t)));
                == {prodCommutesThree(-1,b, prod(q,t));}
                prod(a,1 - prod(q,s)) + prod(b, prod(-1, prod(q,t)));
                linearCombination(a, 1- prod(q,s), b, prod(-1, prod(q,t)));
            }
            assert r in icombinationSet(a,b);
            assert r < d;
            // assert d < r;
            assert false;
        }
        assert r == 0;
        assert a == divAdd(q,d,0);
      
        DivisionAlgorithm(d,b);
        var l,k :| b == divAdd(l,d,k) &&  0 <= k < d;
        if k > 0 {
            calc {
                k;
                b - prod(l,d);
                b - prod(l, linearCombination(a,s,b,t));
                b - prod(l, prod(a,s)+prod(b,t));
                == {prodDistributes(l, prod(a,s), prod(b,t));}
                b - (prod(l, prod(a,s))+prod(l, prod(b,t)));
                == {prodCommutesThree(l,a,s);}
                b - (prod(a, prod(l,s))+prod(l, prod(b,t)));
                == {prodCommutesThree(l,b,t);}
                b - prod(a, prod(l,s)) - prod(b, prod(l,t));
                - prod(a, prod(l,s)) + b - prod(b, prod(l,t));
                == {prodNegative(a, prod(l,s));}
                prod(-1, prod(a, prod(l,s))) + b - prod(b, prod(l,t));
                == {prodCommutesThree(-1, a, prod(l,s));}
                prod(a, prod(-1, prod(l,s))) + b - prod(b, prod(l,t));
                =={ prodIdentity(b);}
                prod(a, prod(-1, prod(l,s))) + prod(b,1) - prod(b, prod(l,t));
                == { prodDistributesMinus(b, 1, prod(l,t));}
                prod(a, prod(-1, prod(l,s))) + prod(b,1 - prod(l,t));
                linearCombination(a, prod(-1, prod(l,s)), b, 1 - prod(l,t));
            }
            assert k in icombinationSet(a,b);
            // assert k < d;
            // assert d < k;
            assert false;
        }
        assert k == 0;
        assert b == divAdd(l,d,0);

        DivAddZero(a,q,d);
        DivAddZero(b,l,d);
        var c := Gcd(a,b);
        FactorIsFactorOfLinearCombination(c,a,b);
    }

}