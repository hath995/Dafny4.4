include "../definitions.dfy"
module CummingsCh3 {
    import opened Analysis

    lemma exercise3_1b(a_i: pos -> real, N: nat)
        requires Limit(a_i, 0.001)
        requires positiveNat(N) && forall n :: n > N ==> converges(a_i, n, 0.001, 0.001)
        ensures forall n:: n > N ==> a_i(n) >= 0.0
    {
        forall n | n > N 
            ensures a_i(n) >= 0.0
        {
            assert converges(a_i, n, 0.001, 0.001);
        }
    }

    method exercise3_1m(a_i: pos -> real) returns (ghost negatives: set<nat>)
        requires Limit(a_i, 0.001)
        ensures forall x :: x in negatives ==> a_i(x) < 0.0
        ensures exists N: nat :: positiveNat(N) && |negatives| <= N
    {
        var epsilon: real := 0.001;
        assert positiveReal(epsilon);
        ghost var N: nat :| positiveNat(N) && forall n :: n > N ==> converges(a_i, n, epsilon, 0.001);
        ghost var i: nat := 1;
        negatives := {};
        while i < N
            invariant 0 <= i <= N
            invariant forall x :: x in negatives ==> a_i(x) < 0.0
            invariant |negatives| <= i
        {
            if a_i(i) < 0.0 {
                negatives := {i} + negatives;
            }
            i := i + 1;
        }
        assert i <= N;
        assert |negatives| <= N;
    }

    lemma multiplyByXoverX(a: real, b: real, x: real)
        requires x != 0.0 && b != 0.0
        ensures a/b == prod(a,x)/prod(b,x)
    {

    }

    lemma subtractLikeBase(denominator: real, x: real, y: real)
        requires denominator != 0.0
        ensures x/denominator-y/denominator == (x-y)/denominator
    {

    }

lemma helper(x: real, y: real, z: real)
    requires x >0.0 && y > 0.0 && z> 0.0
    requires x * y > z * y
    ensures x > z
{

}
lemma biggerDenominator(bigger: nat, smaller: nat)
    requires 0 < smaller < bigger
    ensures (1.0 / smaller as real) > (1.0 / bigger as real)
{
    var delta: pos := bigger - smaller;
    helper((1.0 / smaller as real), ((smaller+delta) as real), (1.0 / (smaller + delta) as real));
}

lemma biggerDenominatorReal(bigger: real, smaller: real)
    requires 0.0 < smaller < bigger
    ensures (1.0 / smaller) > (1.0 / bigger)
{

    var delta := bigger - smaller;
    helper((1.0 / smaller as real), ((smaller+delta) as real), (1.0 / (smaller + delta) as real));
}

    function TwoNminusTwoOverFiveNPlusOne(n: pos): real {
        (2.0*(n as real)-2.0)/(5.0*(n as real)+1.0)
    }

    lemma TwoNminusTwoOverFiveNPlusOneN(n: pos, N: pos, epsilon: real)
        requires epsilon > 0.0
        requires n > N
        requires N == ((12.0/epsilon-5.0)/25.0).Floor+1
        ensures 12.0/(25.0*(n as real)+5.0) < 12.0/(25.0*(N as real)+5.0)
    {}

    lemma {:verify } exercise3_4b() 
        ensures Limit(TwoNminusTwoOverFiveNPlusOne, 2.0/5.0)
    {

        forall epsilon: real | positiveReal(epsilon)
            ensures exists N: nat :: positiveNat(N) && forall n: pos :: n > N ==> converges(TwoNminusTwoOverFiveNPlusOne, n, epsilon, 2.0/5.0)
        {

    /*
            12.0/(25.0*(n as real)+5.0) < 12.0/(25.0*(N as real)+5.0) = epsilon;
            12.0/(25.0*(N as real)+5.0) = epsilon;
            12.0/epsilon-5.0 = 25.0*(N as real)
            (12.0/epsilon-5.0)/25.0 = (N as real)
    */
            if epsilon >= 1.0 {
                assert positiveNat(1);
                forall n: nat | n >1 
                    ensures  12.0/(25.0*(n as real)+5.0) < epsilon
                {
    calc {
                        abs(TwoNminusTwoOverFiveNPlusOne(n)-(2.0/5.0)) ;
                        abs((2.0*(n as real)-2.0)/(5.0*(n as real)+1.0)-(2.0/5.0)) ;
                        // {multiplyByXoverX(2.0, 5.0, (5.0*(n as real)+1.0));}
                        abs((2.0*(n as real)-2.0)/(5.0*(n as real)+1.0)-prod(2.0,(5.0*(n as real)+1.0))/prod(5.0,(5.0*(n as real)+1.0))) ;
                        abs((2.0*(n as real)-2.0)/(5.0*(n as real)+1.0)-(2.0*(5.0*(n as real)+1.0))/(5.0*(5.0*(n as real)+1.0))) ;
                        {multiplyByXoverX(2.0*(n as real)-2.0, 5.0*(n as real)+1.0, 5.0);}
                        abs((5.0*(2.0*(n as real)-2.0))/(5.0*(5.0*(n as real)+1.0))-(2.0*(5.0*(n as real)+1.0))/(5.0*(5.0*(n as real)+1.0))) ;
                        abs((10.0*(n as real)-10.0)/(5.0*(5.0*(n as real)+1.0))-((10.0*(n as real)+2.0))/(5.0*(5.0*(n as real)+1.0))) ;
                        abs((10.0*(n as real)-10.0)/(25.0*(n as real)+5.0)-(10.0*(n as real)+2.0)/(25.0*(n as real)+5.0)) ;
                        {subtractLikeBase(25.0*(n as real)+5.0, 10.0*(n as real)-10.0, 10.0*(n as real)+2.0);}
                        abs((10.0*(n as real)-10.0-(10.0*(n as real)+2.0))/(25.0*(n as real)+5.0)) ;
                        abs((10.0*(n as real)-10.0-10.0*(n as real)-2.0)/(25.0*(n as real)+5.0)) ;
                        abs((10.0*(n as real)-10.0*(n as real)-12.0)/(25.0*(n as real)+5.0)) ;
                        abs(-12.0/(25.0*(n as real)+5.0)) ;
                        {assert forall n : pos :: -12.0/(25.0*(n as real)+5.0) < 0.0;}
                        -(-12.0/(25.0*(n as real)+5.0)) ;
                        {assert forall x: real :: --x == x; assert -(-12.0/(25.0*(n as real)+5.0)) == 12.0/(25.0*(n as real)+5.0);}
                        12.0/(25.0*(n as real)+5.0) ;
                    }
                    assert converges(TwoNminusTwoOverFiveNPlusOne, n, epsilon, 2.0/5.0);
                }
            }else{
                var N: nat := ((12.0/epsilon-5.0)/25.0).Floor+1;
                assert positiveNat(N);

                forall n: pos | n > N
                    ensures converges(TwoNminusTwoOverFiveNPlusOne, n, epsilon, 2.0/5.0)
                {
                    calc {
                        abs(TwoNminusTwoOverFiveNPlusOne(n)-(2.0/5.0)) ;
                        abs((2.0*(n as real)-2.0)/(5.0*(n as real)+1.0)-(2.0/5.0)) ;
                        // {multiplyByXoverX(2.0, 5.0, (5.0*(n as real)+1.0));}
                        abs((2.0*(n as real)-2.0)/(5.0*(n as real)+1.0)-prod(2.0,(5.0*(n as real)+1.0))/prod(5.0,(5.0*(n as real)+1.0))) ;
                        abs((2.0*(n as real)-2.0)/(5.0*(n as real)+1.0)-(2.0*(5.0*(n as real)+1.0))/(5.0*(5.0*(n as real)+1.0))) ;
                        {multiplyByXoverX(2.0*(n as real)-2.0, 5.0*(n as real)+1.0, 5.0);}
                        abs((5.0*(2.0*(n as real)-2.0))/(5.0*(5.0*(n as real)+1.0))-(2.0*(5.0*(n as real)+1.0))/(5.0*(5.0*(n as real)+1.0))) ;
                        abs((10.0*(n as real)-10.0)/(5.0*(5.0*(n as real)+1.0))-((10.0*(n as real)+2.0))/(5.0*(5.0*(n as real)+1.0))) ;
                        abs((10.0*(n as real)-10.0)/(25.0*(n as real)+5.0)-(10.0*(n as real)+2.0)/(25.0*(n as real)+5.0)) ;
                        {subtractLikeBase(25.0*(n as real)+5.0, 10.0*(n as real)-10.0, 10.0*(n as real)+2.0);}
                        abs((10.0*(n as real)-10.0-(10.0*(n as real)+2.0))/(25.0*(n as real)+5.0)) ;
                        abs((10.0*(n as real)-10.0-10.0*(n as real)-2.0)/(25.0*(n as real)+5.0)) ;
                        abs((10.0*(n as real)-10.0*(n as real)-12.0)/(25.0*(n as real)+5.0)) ;
                        abs(-12.0/(25.0*(n as real)+5.0)) ;
                        {assert forall n : pos :: -12.0/(25.0*(n as real)+5.0) < 0.0;}
                        -(-12.0/(25.0*(n as real)+5.0)) ;
                        12.0/(25.0*(n as real)+5.0) ;
                    }

                    TwoNminusTwoOverFiveNPlusOneN(n, N, epsilon);
                    assert 12.0/(25.0*(N as real)+5.0) < epsilon by {
                        var niceN := ((12.0/epsilon-5.0)/25.0);
                        var result := 12.0/(25.0*(N as real)+5.0);
                        assert (((12.0/epsilon-5.0)/25.0).Floor+1 ) as real > niceN;
                        assert N == (((12.0/epsilon-5.0)/25.0).Floor+1 );
                        calc {
                            12.0/(25.0*(((12.0/epsilon-5.0)/25.0))+5.0);
                            12.0/(25.0*((12.0/epsilon-5.0)/25.0)+5.0);
                            12.0/(12.0/epsilon-5.0+5.0);
                            12.0/(12.0/epsilon);
                            epsilon;

                        }
                        
                        assert  (25.0*(N as real)+5.0) > (25.0*niceN+5.0);
                        biggerDenominatorReal((25.0*(N as real)+5.0), 25.0*niceN+5.0);
                        assert 1.0/(25.0*(N as real)+5.0) < 1.0/(25.0*(niceN)+5.0);
                        assert (1.0/(25.0*(N as real)+5.0) )*12.0 == result;
                        assert (1.0/(25.0*(N as real)+5.0) )*12.0 < 1.0/(25.0*(niceN)+5.0)* 12.0;
                        assert 12.0/(25.0*(((12.0/epsilon-5.0)/25.0))+5.0) == 1.0/(25.0*(niceN)+5.0)* 12.0;
                        assert result < 1.0/(25.0*(niceN)+5.0)* 12.0;
                    }
                    assert converges(TwoNminusTwoOverFiveNPlusOne, n, epsilon, 2.0/5.0);
                }
            }
        }
    }

    lemma exercise3_8(a_i: pos -> real, b_i: pos -> real, a: real, b: real)
        requires Limit(a_i, a)
        requires Limit(b_i, b)
        ensures Limit(addSequence(a_i, b_i), a+b)
    {

        forall epsilon: real | positiveReal(epsilon)
            ensures exists N: nat :: positiveNat(N) && forall n: pos :: n > N ==> converges(addSequence(a_i, b_i), n, epsilon, a+b)
        {
            var epsilonOver2 := epsilon / 2.0;
            assert positiveReal(epsilonOver2);
            var N: nat :|  positiveNat(N) && forall n: pos :: n > N ==> converges(a_i, n, epsilonOver2, a);
            var M: nat :|  positiveNat(M) && forall n: pos :: n > M ==> converges(b_i, n, epsilonOver2, b);
            var Q := maxNat(N,M);
            assert positiveNat(Q);
            assert forall n: pos :: n > Q ==> converges(a_i, n, epsilonOver2, a);
            assert forall n: pos :: n > Q ==> converges(b_i, n, epsilonOver2, b);
            forall n: pos | n > Q 
                ensures converges(addSequence(a_i, b_i), n, epsilon, a+b)
            {
                calc {
                    abs(addSequence(a_i, b_i)(n)-(a+b));
                    abs(a_i(n) + b_i(n)-(a+b));
                    abs(a_i(n) + b_i(n)-a-b);
                    abs(a_i(n) -a + b_i(n)-b);
                }
                assert converges(a_i, n, epsilonOver2, a);
                assert converges(b_i, n, epsilonOver2, b);
                assert abs(a_i(n) -a) < epsilonOver2;
                assert abs(b_i(n)-b) < epsilonOver2;
                assert abs(a_i(n) -a + b_i(n)-b) <= abs(a_i(n) -a) + abs(b_i(n)-b);
            }
        }
    }

    lemma exercise3_8b(a_i: pos -> real, a: real, c: real)
        requires Limit(a_i, a)
        ensures Limit(mulSequence(a_i, c), prod(c, a))
    {
        forall epsilon: real | positiveReal(epsilon)
            ensures exists N: nat :: positiveNat(N) && forall n: pos :: n > N ==> converges(mulSequence(a_i, c), n, epsilon, prod(c, a))
        {
            if c > 0.0 {
                var epsilonOverC := epsilon/c;
                assert positiveReal(epsilonOverC);
                var N: nat :|  positiveNat(N) && forall n: pos :: n > N ==> converges(a_i, n, epsilon/c, a);
                forall n: pos | n > N 
                    ensures converges(mulSequence(a_i, c), n, epsilon, prod(c, a))
                {
                    assert converges(a_i, n, epsilonOverC, a);
                    // calc {
                    //     abs(mulSequence(a_i, c)(n)-prod(c,a));
                    //     abs(prod(c,a_i(n))-prod(c,a));
                    //     abs(c*a_i(n)-c*a);
                    //     abs(c*(a_i(n)-a));
                    // }
                    var dist := abs(a_i(n)-a);
                    assert 0.0 <= dist < epsilonOverC;
                    inequalitProduct(dist, epsilonOverC, c);
                    assert c*0.0 <= c * dist < c * epsilonOverC;
                    assert c * epsilon/c == epsilon;
                    assert epsilonOverC == epsilon/c;
                    // assert c * epsilonOverC == epsilon;
                    // assert c*0.0 <= c * dist < epsilon;
                    // assert 0.0 < c*epsilon;
                    // assert c * abs(a_i(n)-a) < c*epsilon;
                    var diff := a_i(n)-a;
                    // absThings(diff,c);
                    // assert c *dist == abs(c*diff);
                    // assert c * abs(diff) == abs(c*diff); 
                    // assert abs(c*diff) == abs(c*(a_i(n)-a));
                    // assert abs(c*(a_i(n)-a)) < epsilon; 
                    // assert abs(mulSequence(a_i, c)(n)-prod(c,a)) == abs(c*(a_i(n)-a));
                    assert abs(mulSequence(a_i, c)(n)-prod(c,a)) < epsilon;
                    assert converges(mulSequence(a_i, c), n, epsilon, prod(c, a));
                }
            }else if c == 0.0 {
                var N: nat :|  positiveNat(N) && forall n: pos :: n > N ==> converges(a_i, n, epsilon, a);
                forall n: pos | n > N 
                    ensures converges(mulSequence(a_i, c), n, epsilon, prod(c, a))
                {
                }
            }else {
                var epsilonOverC := -epsilon/c;
                assert positiveReal(epsilonOverC);
                var N: nat :|  positiveNat(N) && forall n: pos :: n > N ==> converges(a_i, n, epsilonOverC, a);
                forall n: pos | n > N 
                    ensures converges(mulSequence(a_i, c), n, epsilon, prod(c, a))
                {

                    assert converges(a_i, n, epsilonOverC, a);
                    // calc {
                    //     abs(mulSequence(a_i, c)(n)-prod(c,a));
                    //     abs(prod(c,a_i(n))-prod(c,a));
                    //     abs(c*a_i(n)-c*a);
                    //     abs(c*(a_i(n)-a));
                    // }
                    var dist := abs(a_i(n)-a);
                    assert 0.0 <= dist < epsilonOverC;
                    // inequalitProduct(dist, epsilonOverC, c);
                    assert c*0.0 <= -c * dist < -c * epsilonOverC;
                    // assert c * epsilon/c == epsilon;
                    // assert epsilonOverC == -epsilon/c;
                    assert -c * epsilonOverC == epsilon;
                    assert -c*0.0 <= -c * dist < epsilon;
                    // assert 0.0 < -c*epsilon;
                    // assert c * abs(a_i(n)-a) < c*epsilon;
                    var diff := a_i(n)-a;
                    // absThings(diff,-c);
                    // assert -c *dist == abs(c*diff);
                    // assert -c * abs(diff) == abs(c*diff); 
                    assert abs(c*diff) == abs(-c*(a_i(n)-a));
                    // assert abs(c*(a_i(n)-a)) < epsilon; 
                    assert abs(mulSequence(a_i, c)(n)-prod(c,a)) == abs(c*(a_i(n)-a));
                    // assert abs(mulSequence(a_i, c)(n)-prod(c,a)) < epsilon;
                    // assert converges(mulSequence(a_i, c), n, epsilon, prod(c, a));
                }
            }
        }
    }

    lemma helper3(a: real, b: real)
        requires 0.0 < a < b 
        ensures 1.0 / a > 1.0 / b
    {
        var delta: real := b - a;
    }

    lemma oneOverNLessThanEpsilon(epsilon: real, N: nat) 
        requires epsilon > 0.0
        requires N == (1.0 / epsilon).Floor + 1
        ensures 1.0 / N as real < epsilon
    {
        if epsilon > 1.0 {

        }else if epsilon == 1.0 {
            
        }else if epsilon < 1.0 {
            helper3(1.0/epsilon, N as real);
            // assert 1.0 / N as real < 1.0/(1.0/epsilon);
            assert 1.0/(1.0/epsilon) == epsilon;
            // assert 1.0 / N as real < epsilon;
        }
    }

    function oneOverN(n: pos): real {
        1.0 / n as real
    }

    lemma {:verify } exercise3_9() 
        ensures Limit(oneOverN, 0.0)
    {
        forall epsilon: real | positiveReal(epsilon)
            ensures exists N: nat :: positiveNat(N) && forall n: pos :: n > N ==> converges(oneOverN, n, epsilon, 0.0)
        {
            var N: nat := (1.0 / epsilon).Floor + 1;
            assert positiveNat(N);
            forall n: pos | n > N
                ensures converges(oneOverN, n, epsilon, 0.0)
            {
                biggerDenominator(n,N);
                oneOverNLessThanEpsilon(epsilon, N);
                assert 1.0 / N as real < epsilon;
                assert abs(oneOverN(n)-0.0) < epsilon; //figured out that 1.0/n < 1.0/ N < epsilon
                //figured out that f(n) < f(N) < epsilon
            }
        }
    }

    lemma {:verify false} exercise3_13(a_i: pos -> real, b_i: pos -> real, a: real, b: real)
        requires Limit(a_i, a)
        requires Limit(b_i, b)
        ensures Limit(subSequence(a_i, b_i), a-b)
    {
        // exercise3_8(a_i, b_i, a, b);
    }
}