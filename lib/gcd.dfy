module Math {
    //imported from https://github.com/dafny-lang/dafny/blob/master/Test/dafny4/gcd.dfy
    type pos = x: nat | 1 <= x witness 1
    ghost predicate IsFactor(p: pos, x: pos) {
        exists q: pos ::  p * q == x
    }

    ghost function Factors(x: pos): set<pos> {
        set p: pos | p <= x  && IsFactor(p, x)
    }

    ghost predicate IsFactorNat(p: nat, x: nat) {
        exists q: nat ::  p * q == x
    }

    ghost function FactorsNat(x: nat): set<nat> {
        set p: nat | p <= x  && IsFactorNat(p, x)
    }

    lemma FactorsNatNotZero(x: nat)
        requires x!=0
        ensures forall y :: y in FactorsNat(x) ==> y > 0
    {}


    lemma FactorsNatEquiv(x: nat)
        requires x!=0
        ensures FactorsNat(x) == Factors(x)
    {
        
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

    lemma FactorsNotEmpty(x: pos)
        ensures Factors(x) != {}
    {
        FactorsContains1(x);
    }

    lemma prodFactors(x: pos, y: pos)
        ensures Factors(x) <= Factors(x*y)
        ensures Factors(y) <= Factors(x*y)

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

    lemma AboutGcd2(x: pos, y: pos)
        ensures Gcd(x, y) in Factors(x)
        ensures Gcd(x, y) in Factors(y)
    {
    }

    lemma FactorLessThan(p: pos, x: pos)
        requires IsFactor(p, x)
        ensures p <= x
    {}

    ghost function GcdAll(xs: set<pos>): pos
        requires |xs| > 0
    {
        if |xs| == 1 then
            var x :| x in xs;
            x
        else
            assert exists x :: x in xs && xs - {x} != {} by {
                var x :| x in xs;
                assert |xs - {x}| > 0;
            }
            var x, y :| x in xs && y in xs && x != y;
            Gcd(Gcd(x,y), GcdAll(xs-{x}))
    }

    ghost function GcdAll2(xs: set<pos>): pos
        requires |xs| > 0
    {
        if |xs| == 1 then
            var x :| x in xs;
            x
        else
            assert exists x :: x in xs && xs - {x} != {} by {
                var x :| x in xs;
                assert |xs - {x}| > 0;
            }
            var x :| x in xs;
            Gcd(x, GcdAll2(xs-{x}))
    }

    ghost function FactorUnion(xs: set<pos>): set<pos>
        requires |xs| > 0
    {
        if |xs| == 1 then
            var x :| x in xs;
            Factors(x)
        else
            var x :| x in xs;
            Factors(x) * FactorUnion(xs-{x})
    }

    lemma FactorUnionNotEmpty(xs: set<pos>)
        requires xs != {}
        ensures FactorUnion(xs) != {}
        ensures 1 in FactorUnion(xs)
    {
        if |xs| == 1 {
            var x :| x in xs && FactorUnion(xs) == Factors(x);
            assert Factors(x) != {} by {
                FactorsNotEmpty(x);
            }
            FactorsContains1(x);

        }else{
            var x :| x in xs && FactorUnion(xs) == Factors(x) * FactorUnion(xs-{x});
            assert Factors(x) != {} by {
                FactorsNotEmpty(x);
            }
            FactorsContains1(x);
            FactorUnionNotEmpty(xs-{x});

        }
    }

    lemma FactorUnionCase(xs: set<pos>)
        requires |xs| > 0
        ensures 1 in FactorUnion(xs)
    {
        if |xs| == 1 {
            var x :| x in xs;
            FactorsContains1(x);
            assert 1 in Factors(x);
        }else{
            var x :| x in xs && FactorUnion(xs) == Factors(x) * FactorUnion(xs-{x});
            FactorsContains1(x);
            FactorUnionCase(xs-{x});
            // assert 1 in Factors(x) * FactorUnion(xs-{x});
            // assert 1 in FactorUnion(xs);
        }
    }

    lemma {:vcs_split_on_every_assert} GcdAllFactorIntersection(xs: set<pos>)
        requires |xs| > 0
        requires forall x,y :: x in xs && y in xs && x != y ==> Gcd(x,y) != 1
        requires FactorUnion(xs) != {}
        ensures GcdAll2(xs) == Max(FactorUnion(xs))
    {
        if |xs| == 1 {
            var x :| x in xs && GcdAll2(xs) == x;
            GcdIdempotent(x);
            AboutGcd(x, x);
            assert Gcd(x, x) == x;
            assert GcdAll2(xs) == x;
            assert forall p: pos :: IsFactor(p, x) && IsFactor(p, x) ==> p <= x;
            assert FactorUnion(xs) == Factors(x) by {
                assert |xs| == 1;
                assert |xs-{x}| == 0;
                assert xs - {x} == {};
            }
            assert forall y :: y in Factors(x) ==> y <= x;
            assert GcdAll2(xs) == Max(FactorUnion(xs));
        }else{
            var x :| x in xs && GcdAll2(xs) == Gcd(x, GcdAll2(xs-{x}));
            assert |xs| > 1;
            assert xs-{x} != {};
            assert forall y :: y in xs-{x} ==> Factors(y) !={} by {
                forall y | y in xs-{x}
                    ensures Factors(y) != {}
                {
                    FactorsNotEmpty(y);
                }
            }
            assert FactorUnion(xs-{x}) != {} by {
                FactorUnionNotEmpty(xs-{x});
            }
            GcdAllFactorIntersection(xs-{x});
            assume Factors(x) * Factors(GcdAll2(xs-{x})) == FactorUnion(xs);


            // assert GcdAll2(xs) == Max(FactorUnion(xs));
        }
    }

    // lemma {:vcs_split_on_every_assert} GcdAllValue(xs: set<pos>)
    //     requires |xs| > 1
    //     requires forall x :: x in xs ==> x != 1
    //     requires forall x,y :: x in xs && y in xs && x != y ==> Gcd(x,y) != 1
    //     // ensures forall x, y :: x in xs && y in xs && x != y==> GcdAll(xs) <= Gcd(x, y)
    //     ensures GcdAll(xs) != 1
    //     // ensures forall x :: x in xs ==> IsFactor(GcdAll(xs), x)
    // {
    //     if |xs| == 1 {

    //         assert GcdAll(xs) != 1;
    //     } else if |xs| == 2 {
    //         assert exists x :: x in xs && xs - {x} != {} by {
    //             var x :| x in xs;
    //             assert |xs - {x}| > 0;
    //         }
    //         var x, y :| x in xs && y in xs && y != x;
    //         assert Gcd(x,y) != 1;
    //         assert GcdAll(xs) != 1;
    //     }else{

    //     }
    // }
        

    lemma {:verify false} {:vcs_split_on_every_assert} AllNotCoprime(xs: set<pos>) returns (mingcd: pos)
        requires |xs| > 1
        requires forall x :: x in xs ==> x != 1
        requires forall x,y :: x in xs && y in xs && x != y ==> Gcd(x,y) != 1
        ensures forall x, y :: x in xs && y in xs && x != y==> mingcd <= Gcd(x, y)
        // ensures forall x :: x in xs ==> IsFactor(mingcd, x)
    {
        var gcds := set x,y | x in xs && y in xs && x != y :: Gcd(x,y);
        assert 1 !in gcds;
        var x :| x in xs;
        assert xs-{x} != {} by {
            assert |xs-{x}| > 0;
        }
        var y :| y in xs && y != x;
        assert Gcd(x,y) in gcds;
        assert gcds != {};
        mingcd := Min(gcds);
        forall x, y | x in xs && y in xs && x != y
            ensures mingcd <= Gcd(x, y)
        {
           assert Gcd(x,y) in gcds; 
        }
        // forall x | x in xs
        //     ensures IsFactor(mingcd, x)
        // {
        //    if !IsFactor(mingcd, x) {
        //     var mx, my :| mx in xs && my in xs && mx != my && mx != x && my != x && Gcd(mx, my) == mingcd;
        //     assert Gcd(mx, x) != 1;
        //     assert Gcd(my, x) != 1;
        //     AboutGcd(mx, x);
        //     AboutGcd(my, x);
        //     AboutGcd(mx, my);
        //     AboutGcd2(mx, my);
        //     AboutGcd2(mx, x);
        //     AboutGcd2(my, x);
        //     assert IsFactor(mingcd, mx);
        //     assert IsFactor(mingcd, my);
        //     assert mingcd in Factors(mx);
        //     assert mingcd in Factors(my);
        //     assert mingcd !in Factors(x);
        //     var xfs := Factors(x);
        //     var yfs := Factors(my);
        //     var mxfs := Factors(mx);
        //     assert xfs * yfs != {1};
        //     assert xfs * mxfs != {1};
        //     var gx := Gcd(mx, x);
        //     var gy := Gcd(my, x);
        //     var p: pos :| gx * p == x;
        //     var q: pos :| gy * q == x;
        //     var t: pos :| gx * t == mx;
        //     var u: pos :| gy * u == my;
        //     assert false;
        //    } 
        // }
    }

    lemma GcdSymmetric(x: pos, y: pos)
        ensures Gcd(x, y) == Gcd(y, x)
    {
        assert Factors(x) * Factors(y) == Factors(y) * Factors(x);
    }

    lemma FactorsWithin(p: pos, x: pos)
        requires p in Factors(x)
        ensures forall y :: y in Factors(p) ==> y in Factors(x)
    {
        forall y | y in Factors(p)
            ensures y in Factors(x)
        {
            var q :| p * q == x;
            var z :| y * z == p;
            calc {
                x;
                p*q;
                y*z*q;
            }
            var t := z*q;
            assert y*t ==x;
            assert IsFactor(y, x);
            // assert y*z*q == x;
        }
    }

    lemma FactorsMult(x: pos, y: pos)
        ensures Factors(x*y) == set d_x, d_y | d_x in Factors(x) && d_y in Factors(y) :: d_x * d_y

    lemma Divides(p: pos, y: pos, x: pos)
        requires x in Factors(p*y)
        // requires IsFactor(x ,p*y)
        ensures IsFactor(x, p) || IsFactor(x, y)
    // {
    //     assert x <= p*y;
    //     var z: pos :| x * z == p*y;
    //     // assert (p*y)/x == z;
    //     assert z != 0;
    //     assert z * x == p*y;
    //     assert IsFactor(z, p*y);
    //     if !IsFactor(x,p) {
    //         // assert IsFactor(p, x*z);
    //         assert x*z/p == y;
    //         assert z % p == 0 by {
    //         }
    //         assert !(exists qq: pos :: x * qq == p);
    //         assert IsFactor(x,y);
    //     }
            

    // }

    // lemma notFactor(p: pos, x: pos)
    //     requires !IsFactor(p,x)
    //     ensures p > x || (p < x && exists k :: k in Factors(p) && !IsFactor(k, x))
    // {
    //     if p > x {
    //     }else{
    //     }
    // }

    lemma {:verify false} GcdRest(x: pos, y: pos, s: pos, t: pos)
        requires Gcd(x,y) * s == x
        requires Gcd(x,y) * t == y
        ensures Gcd(s,t) == 1
        ensures Factors(s) * Factors(t) == {1}
    {
        assert s * Gcd(x,y) == x;
        assert IsFactor(s, x);
        assert t * Gcd(x,y) == y;
        assert IsFactor(t, y);
        AboutGcd(x,y);
        if Gcd(s,t) != 1 {
            var p :| Gcd(s,t) * p == s;
            var q :| Gcd(s,t) * q == t;
            calc {
                x;
                Gcd(x,y) * s;
                Gcd(x,y) * Gcd(s,t) * p;
            }

            assert IsFactor(Gcd(x,y) * Gcd(s,t), x);
            calc {
                y;
                Gcd(x,y)*t;
                Gcd(x,y)*Gcd(s,t)*q;
            }
            assert IsFactor(Gcd(x,y)*Gcd(s,t), y);
            assert false;
        }
        FactorsContains1(s);
        FactorsContains1(t);
        if Factors(s) * Factors(t) != {1} {
            assert Factors(s) * Factors(t) != {};
            var x :| x in Factors(s) * Factors(t) && x != 1;
            assert false;
        }
    }

    lemma GcdFactors(x: pos, y: pos)
        ensures Factors(x) * Factors(y) == Factors(Gcd(x,y))
    {
        AboutGcd(x,y);
        FactorsContainsSelf(Gcd(x,y));
        // assert Gcd(x,y) <= x;
        // assert Gcd(x,y) <= y;
        var s :| Gcd(x,y) * s == x;
        // assert s * Gcd(x,y) == x;
        var t :| Gcd(x,y) * t == y;
        // assert t * Gcd(x,y) == y;
        // GcdRest(x,y, s, t);
        assert forall p: pos :: p in Factors(x)*Factors(y) ==> p in Factors(Gcd(x,y)) by {
            GcdGreatest(x, y);
        }
        assert forall p: pos :: p in Factors(Gcd(x,y)) ==> p in Factors(x)*Factors(y) by {
            forall p: pos | p in Factors(Gcd(x,y))
                ensures p in Factors(x)*Factors(y)
            {
                var q :| p * q == Gcd(x,y);
                assert q * p == Gcd(x,y);
                var s' := q*s;
                assert p * s' == x;
                var t' := q*t;
                assert p * t' == y;
                assert IsFactor(p, x);
                assert IsFactor(p, y);
            }
        }
    }

    lemma GcdAssociative(x: pos, y: pos, z: pos)
        ensures Gcd(x, Gcd(y,z)) == Gcd(Gcd(x,y), z)
    {
        assert Factors(x) * Factors(Gcd(y,z)) == Factors(Gcd(x,y)) * Factors(z) by {
            GcdFactors(y,z);
            GcdFactors(x,y);

        }
    }

    lemma GcdIdempotent(x: pos)
        ensures Gcd(x, x) == x
    {
        FactorsContainsSelf(x);
        assert x in Factors(x) * Factors(x);
    }
    
    lemma FactorsLessThanX(x: pos)
        ensures forall p :: p in Factors(x) ==> p <= x
    {}

    lemma GcdIdempotent2(x: pos, y: pos)
        ensures Gcd(Gcd(x, y), x) == Gcd(x,y)
        ensures Gcd(Gcd(x, y), y) == Gcd(x,y)
    {
        FactorsContainsSelf(Gcd(x,y));
        AboutGcd(x,y);
        var common := Factors(Gcd(x,y)) * Factors(x);
        assert 1 in common by {
            FactorsContains1(x);
            FactorsContains1(Gcd(x,y));
        }
        FactorsLessThanX(Gcd(x,y));
        assert Gcd(x,y) in Factors(x);
        assert Gcd(x,y) in Factors(Gcd(x, y));
        assert Gcd(x,y) in common;
        assert Max(common) == Gcd(x,y);
        var commony := Factors(Gcd(x,y)) * Factors(y);
        assert Gcd(x,y) in Factors(y);
        assert Gcd(x,y) in commony;
        assert Max(commony) == Gcd(x,y);
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

    function Euclid(x: nat, y: nat): nat 
        decreases y, x
    {
        if y == 0 then 
            x
        else
            Euclid(y, x % y)
    }

    lemma AboutEuclid(x: nat, y: nat)
        requires y == 0
        requires x > 0
        ensures Euclid(x,y) > 0
    {}

    lemma AboutEuclid2(x: pos, y: pos)
        ensures Euclid(x,y) > 0
    {
        if x < y {
            EuclidMod2(x,y);

        }else{

        }
    }

    lemma EuclidGcdEquivalence(x: pos, y: pos)
        ensures Euclid(x,y) == Gcd(x,y)
    {
        AboutEuclid2(x, y);
        FactorsNatEquiv(x);
        FactorsNatEquiv(y);
        FactorsNatEquiv(Gcd(x,y));
        AboutGcd(x, y);
        EuclidGreatest(x, y);
        EuclidDivisor(x, y);
        var gcde := Euclid(x, y);
        var ggcd := Gcd(x, y);
        assert gcde <= Gcd(x, y);
        assert gcde >= Gcd(x, y);

    }

    lemma EuclidDivisor(x: pos, y: pos)
        requires Euclid(x,y) > 0
        ensures IsFactor(Euclid(x,y), x)
        ensures IsFactor(Euclid(x,y), y)
        decreases y,x
    {
        if x % y == 0 {
            calc {
                Euclid(x,y);
                Euclid(y, 0);
                y;
            }
            assert y * 1 == y;
            assert IsFactor(y, y);
            var k: nat := x / y;
            assert y * k == x;
            assert IsFactor(y, x);

        }else{
            calc {
                Euclid(x, y);
                Euclid(y, x%y);
            }
            EuclidDivisor(y, x%y);
            var q :| Euclid(y, x%y) * q == (x%y);
            var s :| Euclid(y, x%y) * s == y;
            assert y*(x / y) + x%y == x;
            calc {
                x;
                y*(x / y) + x%y;
                y*(x / y) + Euclid(y, x%y) * q;
                (Euclid(y, x%y) * s)*(x / (Euclid(y, x%y) * s)) + Euclid(y, x%y) * q;
                Euclid(y, x%y) * (s*(x / y) + 1 * q);
            }

            assert IsFactor(Euclid(x,y), x);
            assert IsFactor(Euclid(x,y), y);
        }
    }

    lemma EuclidSymmetric(x: nat, y: nat)
        ensures Euclid(x, y) == Euclid(y, x)
    {
        if y == 0 {

        }
    }

    lemma EulerIdempotent(x: nat)
        ensures Euclid(x,x) == x
    {}

    lemma EuclidMod2(x: nat, y: nat)
        requires 0 < x < y
        ensures Euclid(x, y) == Euclid(x, y % x)
    { 
        EuclidSymmetric(x, y);
    }

    // lemma EulerSubtract(x: nat, y: nat)
    //     requires x < y
    //     ensures Euclid(x, y) == Euclid(x, y-x)
    // {
    //     var p := Euclid(x, y);
    // }

    lemma ModPosLemma(x: pos, y: pos, z: pos)
        requires x < y
        requires IsFactor(z, x)
        requires IsFactor(z, y)
        ensures IsFactor(z, y - x)
    {
        var p :| z * p == x;
        var q :| z * q == y;
        assert q > p;
        // assert p - q * (x/y) > 0;
        calc {
            y - x;
            z * q - z * p;
            z * (q-p);
        }
        assert IsFactor(z, y - x);
    }
    
    lemma ModLemma(x: nat, y: pos, z: nat)
        requires IsFactorNat(z, x)
        requires IsFactorNat(z, y)
        ensures IsFactorNat(z, x % y)
    {
        if x % y == 0 {
            assert z * 0 == x % y;
            assert IsFactorNat(z, x % y);
        }else if x < y {

        }else{
            assert x > y by {
                if x == 0 {

                }
            }
            var p :| z * p == x;
            var q :| z * q == y;
            assert p >= q;
            // assert p - q * (x/y) > 0;
            calc {
                x % y;
                x - y*(x/y);
                (z*p) - (z*q)*(x/y);
                z *(p - q * (x/y));
            }
            assert IsFactorNat(z, x);
        }
    }

    lemma {:verify false}EuclidMod(x: pos, y: pos)
        ensures IsFactorNat(Euclid(x, y), x % y)
    {
        AboutEuclid2(x, y);
        EuclidDivisor(x, y);
        if x % y == 0 {
            var g: nat := x/y;
            assert Euclid(x,y) * 0 == x%y;

            assert IsFactorNat(Euclid(x,y), x);
        } else if x < y {
            assert x % y == x;
            assert IsFactorNat(Euclid(x,y), x);
        }else{
            assert x > y by {
                if x == y {
                }
            }
            var p :| Euclid(x,y) * p == x;
            var q :| Euclid(x,y) * q == y;
            assert p >= q;
            assert p - q * (x/y) > 0;
            calc {
                x % y;
                x - y*(x/y);
                (Euclid(x,y)*p) - (Euclid(x,y)*q)*(x/y);
                Euclid(x,y) *(p - q * (x/y));
            }
            assert IsFactorNat(Euclid(x,y), x);
        }
    }
    
    lemma GcdGreatest(x: pos, y: pos)
        ensures forall z :: z in Factors(x) * Factors(y) ==> IsFactor(z, Gcd(x,y))
        decreases x + y
    {
        forall z | z in Factors(x) * Factors(y)
            ensures IsFactor(z, Gcd(x, y))
        {
            if x == y {
                GcdIdempotent(x);
                assert IsFactor(z, Gcd(x, y));
            }else if x < y {
                ModPosLemma(x, y, z);
                GcdSubtract(x, y);
                GcdGreatest(x, y - x);
                assert IsFactor(z, Gcd(x, y));
            }else{
                ModPosLemma(y, x, z);
                GcdSymmetric(x, y);
                GcdSubtract(y, x);
                GcdGreatest(y, x - y);
                assert IsFactor(z, Gcd(x, y));
            }
        }
    }

    lemma EuclidGreatest(x: nat, y: nat)
        ensures forall z :: z in FactorsNat(x)*FactorsNat(y) ==> IsFactorNat(z, Euclid(x,y))
        decreases y, x
    {
        forall z |  z in FactorsNat(x)*FactorsNat(y)
            ensures IsFactorNat(z, Euclid(x,y))
        {
            if y == 0 {
                assert IsFactorNat(z, Euclid(x,y));
            }else{
                if x == 0 {
                    assert IsFactorNat(z, Euclid(x,y));
                }else{
                    assert x > 0;
                    assert y > 0;
                    ModLemma(x, y, z);
                    assert IsFactorNat(z, x % y);
                    EuclidGreatest(y, x % y);

                }

            }
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