include "definitions.dfy"
module AnalysisExercises {
import opened Analysis



lemma NaturalFraction(i: pos, k: pos)
    requires i >= k
    ensures 1.0/(i as real) <= 1.0/(k as real)
{
    if i == 1 {
        assert k == 1;
    }else{

    }
}

lemma smallerThan1(a: real)
    requires 0.0 < a < 1.0
    ensures 0.0 < a*a < a < 1.0
{
}

lemma noZeroDivisor(a: real, b: real)
    requires a != 0.0 && b != 0.0
    ensures a*b != 0.0
{}

lemma smallerThanR(r: real, rs: real)
    requires 0.0 < r < 1.0
    requires rs == r*r
    ensures 0.0 < rs*rs < r < 1.0
{
    smallerThan1(r);
    assert 0.0 < r*r < r;
    if r*r == 0.0 {
        noZeroDivisor(r,r);
        assert false;
    }
    smallerThan1(rs);
}

lemma multLte(a: real, b: real, c: real)
    requires c > 0.0
    requires a < b
    ensures a*c < b *c
{}


lemma uGreater(u: real, r: real)
    requires u > 0.0 && r > 0.0
    requires u*u > r*r
    ensures u > r
{
    if u >= 1.0 {
    }else{
        // assert 0.0 < u < 1.0;
        // multLte(u, 1.0, u);
        // assert u*u < u*1.0;
        // assert u * u < u;
    }
}

//https://proofwiki.org/wiki/Existence_of_Square_Roots_of_Positive_Real_Number
lemma {:vcs_split_on_every_assert} sqrtExists(r: real)
    requires r > 0.0
    ensures exists y :: r == y * y
{
    if r == 1.0 {
        assert r == r*r;
    }else{
    var S := iset x | x*x < r ;
    assert upperBound(S, r+1.0);
    forall x | x in S 
        ensures x < r+1.0
    {}

    forall y | y > r+1.0
        ensures y*y !in S
    {
        var r' := r +1.0;
        assert r' > 1.0;
        assert y > 1.0;
        assert y > r';
    }
    assert 0.0 in S;
    assert forall x :: x in S ==> x < r+1.0;
    CompletenessAxiomUpper(S,r+1.0);
    var u :| sup(S, u);
    if u*u > r {
        assert u > 0.0;
        ArchimedeanPrinciple((u*u-r)/(2.0*u));
        assert 0.0 < (u*u-r)/(2.0*u);
        var n: pos :| 1.0/(n as real) < (u*u-r)/(2.0*u);
        var u' := (u-1.0/(n as real));
        assert u' == sub(u,1.0/(n as real));
        calc {
            u-(u*u-r)/(2.0*u);
            (2.0*u)*u/(2.0*u)-(u*u-r)/(2.0*u);
            ((2.0*u)*u-(u*u-r))/(2.0*u);
            (u*u+r)/(2.0*u);
        }
        assert 0.0 < 1.0/(n as real) < u;
        assert u' > 0.0;
        calc{
            u'*u';
            (u-1.0/(n as real))*(u-1.0/(n as real));
            u*u-(2.0*u/(n as real))+1.0/((n as real)*(n as real));
        }
       
        assert u'*u' > u*u-(2.0*u/(n as real));
        assert u*u-(2.0*u/(n as real)) > r by {
            assert (n as real) >= 1.0;
            assert u > 0.0;
            calc {
                1.0/(n as real) < (u*u-r)/(2.0*u);
                {multLte((1.0/(n as real)),((u*u-r)/(2.0*u)),2.0*u);}
                (2.0*u)*(1.0/(n as real)) < (2.0*u)*((u*u-r)/(2.0*u));
            }
        }
        assert u'*u' > r;
        assert upperBound(S, u') by {
            forall x | x in S
                ensures x < u'
            {
                assert x*x < r < u'*u';
                assert x*x < u'*u';
                if x <= 0.0 {
                }else{
                    uGreater(u',x);
                }
            }
        }
        assert false;
    }
    if u*u < r {
        assert upperBound(S, u);
        assert u in S;
        if u < 0.0 {
            assert !upperBound(S, u);
            assert false;
        }else if u > 0.0 {
            assert (r-u*u)/(4.0*u) > 0.0;
            ArchimedeanPrinciple((r-u*u)/(4.0*u));
            ArchimedeanPrinciple(2.0*u);
            var na: pos :| 1.0 / (na as real) < ((r-u*u)/(4.0*u));
            var nb: pos :| 1.0 / (nb as real) < (2.0*u);
            var n := if na > nb then na else nb;
            NaturalFraction(n, nb);
            NaturalFraction(n, na);
            var nf := 1.0 / (n as real);
            assert nf > 0.0;
            assert 1.0 / (n as real) < 2.0*u;
            assert nf < 2.0*u;
            assert 1.0 / (n as real) < ((r-u*u)/(4.0*u));
            var u' := u+1.0/(n as real);
            calc {
                u'*u';
                (u+1.0/(n as real))*(u+1.0/(n as real));
                u*u+(2.0*u/(n as real))+(1.0/((n as real )*(n as real)));
            }
            calc {
                nf * nf;
                (1.0/((n as real )*(n as real)));
            }
            calc {
                nf * 2.0*u;
                (2.0*u/(n as real));
            }
            multLte(nf,2.0*u,nf);
            assert nf * nf < nf *(2.0*u);
            assert (1.0/((n as real )*(n as real))) < (2.0*u/(n as real));
            assert u*u+(2.0*u/(n as real))+(1.0/((n as real )*(n as real))) < u*u+(2.0*u/(n as real))+(2.0*u/(n as real));
            calc {
                (2.0*u/(n as real))+(2.0*u/(n as real));
                (4.0*u/(n as real));
            }
            assert r-u*u > 0.0;
            assert r-u*u > (4.0*u/(n as real)) by {
                assert 1.0 / (n as real) < ((r-u*u)/(4.0*u));
                assert (n as real) >= 1.0;
                calc {
                1.0 / (n as real) < ((r-u*u)/(4.0*u));
                (4.0*u)* (1.0 / (n as real)) < (4.0*u)*((r-u*u)/(4.0*u));
                (4.0*u)* (1.0 / (n as real)) < (r-u*u);
                (4.0*u / (n as real)) < (r-u*u);
                }
            }
            assert u*u+(2.0*u/(n as real))+(2.0*u/(n as real)) <= u*u + (r - u*u);
            assert u' * u' < u*u+(2.0*u/(n as real))+(2.0*u/(n as real)) <=r ;
            assert u' * u' < r ;
            assert u' in S;
            assert false;
        }else if u == 0.0 {
            assert upperBound(S, 0.0);
            if r > 1.0 {
                assert 1.0 * 1.0 < r;
                assert 1.0 in S;
                assert false;
            }else {
                assert 0.0 < r < 1.0;
                var rs := r * r;
                smallerThanR(r,rs);
                assert rs in S;
                assert false;
            }
            assert false;
        }
    }
    
    assert u*u == r;
    }
}



lemma stillInt(x: real) 
    requires x.Floor as real == x
    ensures sub(x, 1.0).Floor as real == sub(x, 1.0)
{
    var m: int := x.Floor;
    assert (m-1) as real == sub(x, 1.0);
}

lemma stillIntPlus(x: real) 
    requires x.Floor as real == x
    ensures add(x, 1.0).Floor as real == add(x, 1.0)
{
    var m: int := x.Floor;
    assert (m+1) as real == add(x, 1.0);
}

lemma floorNaturals(nats: iset<real>)
    requires forall x :: x in nats ==> exists k: nat :: k as real == x
    ensures forall x :: x in nats ==> x.Floor as real == x
{

}

function double(n: pos): pos  {
    2 * n
}

lemma doubleIsMonotoneInc() 
    ensures MonotonicIncreasingPos(double)
{}


lemma {:verify false} TEstThing(k: nat, d_i: pos -> pos)
    requires MonotonicIncreasingPos(d_i) 
    // ensures exists k :: positiveNat(k) && d_i(k) > k
{
    assert forall n: pos :: d_i(1) <= d_i(n);
}

lemma {:verify false} sequenceConverges(a_i: pos -> real, k_i: pos -> pos, a: real)
    ensures Limit(a_i, a) <==> forall d_i: pos -> pos :: MonotonicIncreasingPos(d_i) ==> Limit(SubSequenceOf(a_i, d_i), a)
{
    if Limit(a_i, a) {
        forall d_i: pos -> pos | MonotonicIncreasingPos(d_i) 
            ensures Limit(SubSequenceOf(a_i, d_i), a) 
        {
            forall epsilon: real | positiveReal(epsilon) 
                ensures exists LN :: positiveNat(LN) && forall n :: n > LN ==> converges(SubSequenceOf(a_i, d_i), n, epsilon, a)
            {
                var N :| positiveNat(N) && forall n :: n > N ==> converges(a_i, n, epsilon, a);
                var k :| positiveNat(k) && d_i(k) > N;
            }
        }
    }//else if forall d_i: pos -> pos :: MonotonicIncreasingPos(d_i) && Limit(SubSequenceOf(a_i, d_i), a) {

    //}
}

lemma {:verify false} MonotoneSubsequenceConverges(a_i: pos -> real, k_i: pos -> pos, a: real)
    requires MonotonicIncreasingPos(k_i)
    requires Monotone(a_i)
    requires Limit(SubSequenceOf(a_i, k_i), a)
    ensures Limit(a_i, a)
{
    sequenceConverges(a_i, k_i, a);
    assert Limit(a_i, a) ==> forall d_i: pos -> pos :: MonotonicIncreasingPos(d_i) && Limit(SubSequenceOf(a_i, d_i), a);
    assert Limit(a_i, a) <== forall d_i: pos -> pos :: MonotonicIncreasingPos(d_i) && Limit(SubSequenceOf(a_i, d_i), a);
    if !Limit(a_i, a) {
        if !MonotonicIncreasingPos(k_i) {
            assert false;
        }else if !Limit(SubSequenceOf(a_i, k_i), a) {
            assert false;
        }else {
            assert MonotonicIncreasingPos(k_i) && Limit(SubSequenceOf(a_i, k_i), a) ;
            assert !(forall d_i: pos -> pos :: MonotonicIncreasingPos(d_i) && Limit(SubSequenceOf(a_i, d_i), a));
            assert false;
        }
    }
}



lemma smallerX(a: real, b : real)
    requires a > 0.0
    requires 0.0 <= b < 1.0
    ensures b*a < a 
{}

lemma exercise3_18a(a_i: pos -> real, b_i: pos -> real, a_range: iset<real>, al: real, au: real)
    requires Limit(b_i, 0.0)
    requires a_range == iset n: pos | positiveNat(n) :: a_i(n)
    requires al <= au
    requires bounded(a_range, al, au) && boundedSeq(a_i, al, au)
    ensures Limit(prodSequence(a_i, b_i), 0.0)
{
    assert al <= au;
    forall epsilon: real | positiveReal(epsilon)
        ensures exists N: nat :: positiveNat(N) && forall n: pos :: n > N ==> converges(prodSequence(a_i, b_i), n, epsilon, 0.0)
    {
        var max := maxReal(abs(al), abs(au))+1.0;
        var epsilonOverMax := div(epsilon , max);
        assert positiveReal(epsilonOverMax);
        var N: nat :|  positiveNat(N) && forall n: pos :: n > N ==> converges(b_i, n, epsilonOverMax, 0.0);
        forall n: pos | n > N 
            ensures converges(prodSequence(a_i, b_i), n, epsilon,  0.0)
        {
            assert converges(b_i, n, epsilonOverMax, 0.0);
            assert abs(b_i(n)-0.0) < epsilonOverMax;
            assert abs(b_i(n)) < epsilonOverMax;
            calc {
            abs(prodSequence(a_i, b_i)(n)-0.0); 
            abs(prodSequence(a_i, b_i)(n)); 
            abs(prod(a_i(n), b_i(n))); 
            }
            absProd(a_i(n), b_i(n));
            // assert prod(abs(a_i(n)) , abs(b_i(n))) == abs(prod(a_i(n), b_i(n)));
            // assert abs(b_i(n)) < epsilonOverMax;
            assert prod(abs(a_i(n)) , epsilonOverMax) < epsilon by {
                assert al <= a_i(n) <= au;
                var an := abs(a_i(n));
                assert an >= 0.0;
                var bx:=div(an,max); 
                assert bx >= 0.0;
                calc {
                    prod(abs(a_i(n)),  div(epsilon , max));
                    prod(an,  div(epsilon , max));
                    {divCommute(an, epsilon, max);}
                    prod(div(an , max) , epsilon);
                    prod(bx , epsilon);
                    (bx) * epsilon;
                }
                if abs(al) >= abs(au) {
                    // assert abs(a_i(n)) <= abs(al) < max;
                    divSmaller(abs(a_i(n)), max);
                    assert abs(a_i(n))/max < 1.0;
                    smallerX(epsilon, bx);
                    // assert (bx) * epsilon < epsilon;
                    // assert (abs(a_i(n)) / max) * epsilon < epsilon;
                    // assert bx == abs(a_i(n)) / max;
                    // assert (bx) * epsilon == prod(abs(a_i(n)) , div(epsilon , max));
                    assert prod(abs(a_i(n)) , div(epsilon , max)) < epsilon;
                }else{
                    assert abs(a_i(n)) <= abs(au) < max;
                    divSmaller(abs(a_i(n)), max);
                    assert abs(a_i(n))/max < 1.0;
                    // assert 0.0 <= bx < 1.0;
                    smallerX(epsilon, bx);
                    // assert (bx) * epsilon < epsilon;
                    // assert (bx) * epsilon == prod(abs(a_i(n)) , div(epsilon , max));
                    assert prod(abs(a_i(n)) , div(epsilon , max)) < epsilon;
                }
            }
            // assert abs(prodSequence(a_i, b_i)(n)-0.0) ==abs(prod(a_i(n), b_i(n)));  
            if abs(a_i(n)) == 0.0 {
                // assert prod(abs(a_i(n)),abs(b_i(n)))  < epsilon;
                // assert abs(prod(a_i(n), b_i(n))) < epsilon; 
                // assert abs(prodSequence(a_i, b_i)(n)-0.0) < epsilon;
                assert converges(prodSequence(a_i, b_i), n, epsilon, 0.0);
            }else if abs(a_i(n)) > 0.0 {
                // assert abs(a_i(n)) > 0.0;
                prodLessThan(abs(a_i(n)), abs(b_i(n)), epsilonOverMax);
                assert prod(abs(a_i(n)),abs(b_i(n))) < prod(abs(a_i(n)),epsilonOverMax) < epsilon;
                // assert abs(prod(a_i(n), b_i(n))) < epsilon; 
                // assert abs(prodSequence(a_i, b_i)(n)-0.0) < epsilon;
                assert converges(prodSequence(a_i, b_i), n, epsilon, 0.0);
            }
        }

    }
}

ghost function sqrt(x: real) : real 
    ensures sqrt(x)*sqrt(x) == x

function newtonSqrt(n: real, i: pos): real 
    requires n > 0.0
    requires n != 0.0
    ensures newtonSqrt(n,i) != 0.0
    ensures newtonSqrt(n,i) > 0.0
    ensures n == 1.0 ==> newtonSqrt(n,i) == 1.0
{
    if i == 1 then 
        assert n != 0.0;
        n
    else
        var prev := newtonSqrt(n, i-1);
        assert prev != 0.0;
        assert (prev+(n / prev)) != 0.0;
        (prev+(n / prev))/2.0
}

// lemma newtonSqrtGreaterThan1(n: real, i: pos)
//     requires n > 1.0
//     ensures newtonSqrt(n,i) > 1.0
// {
//     if i == 1 {

//     }else{
//         newtonSqrtGreaterThan1(n, i-1);

//     }
// }

function sqrtSeq(n: real): pos -> real
    requires n > 0.0
{
    (i: pos) => newtonSqrt(n,i)
}

lemma sqrtSeqLess(a: real, i: pos)
    requires a >= 1.0
    ensures sqrtSeq(a)(i) >= sqrtSeq(a)(i+1)

lemma sqrtSeqLessAll(a: real, n: pos, m: pos)
    requires a >= 1.0
    requires n < m
    ensures sqrtSeq(a)(n) >= sqrtSeq(a)(m)
{
    if m == n+1 {
        sqrtSeqLess(a, n);
        assert sqrtSeq(a)(n) >= sqrtSeq(a)(m);
    }else{
        assert m-1 > n;
        sqrtSeqLessAll(a, n,m-1);

        assert sqrtSeq(a)(n) >= sqrtSeq(a)(m-1);
        sqrtSeqLess(a, m-1);
        assert sqrtSeq(a)(n) >= sqrtSeq(a)(m);
    }
}
// {
//     if i == 0 {

//     }else{
//         var prev := sqrtSeq(a)(i);
//         calc {
//             sqrtSeq(a)(i+1);
//             (prev+(a/prev))/2.0;
//         }
//         assert a / prev <= 1.0;
//         assert 2.0*prev >= (prev+(a/prev));
//         assert prev > (prev+(a/prev))/2.0;
//     }
// }

lemma real1(a: real)
    requires a != 0.0
    ensures a/a == 1.0
{}

lemma sqrtSeqMonotonic(a: real)
    requires a >= 1.0
    ensures MonotonicDecreasingSequence(sqrtSeq(a))
{
    var sseq := sqrtSeq(a);
    forall n,m | n < m
        ensures sseq(n) >= sseq(m)
    {
        if n == 1 {
            if m == 2 {
                calc {
                    sseq(n);
                    sseq(1);
                    a;
                }
                real1(a);
                assert a/a == 1.0;
                calc {
                    sseq(m);
                    sseq(2);
                    (a+a/a)/2.0;
                    (a+1.0)/2.0;
                }
                // assert a >= (a+1.0)/2.0;
                // assert sseq(1) >= a >=  (a+1.0)/2.0 >= sseq(2) ;
                // assert sseq(1) == sseq(n);
                // assert sseq(2) == sseq(m);
                assert sseq(n) >= sseq(m);
            }else{
                assert m > 2;
                assert sseq(n) >= sseq(m);
            }
        }else{

            assert sseq(n) >= sseq(m);
        }
    }
}

    method calcSqrt(n: real) returns (nroot: real)
    {
    nroot := n; 
    }
}