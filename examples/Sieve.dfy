include "./sqrt.dfy"
module  Sieve {
    import opened SOSqrt
    function {:opaque} prod(x: int, y: int): int {
        x * y
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
    lemma modMultiplication(aone: int, bone: int, atwo: int, btwo: int, n: int)
        requires n != 0
        requires aone % n == bone
        requires atwo % n == btwo
        ensures (aone * atwo) % n == (bone * btwo) % n 

    lemma prodSelfAnnihilation(a: int, b: int) 
        requires a != 0
        ensures prod(a,b) % a == 0
    {
        reveal prod();
        calc {
            (b * a) % a;
            {modMultiplication(a,0,b,b%a,a);}
            (0 * b%a) % a;
            0;
        }
    }
    ghost predicate IsFactor(p: nat, x: nat) {
        exists q: nat ::  prod(p , q) == x
    }

    lemma IsFactorDivides(p: nat, x: nat)
        requires x > 0
        requires p > 0
        requires IsFactor(p, x)
        ensures x % p == 0
    {
        var q : nat :| prod(p, q) == x;
        if q == 0 {
            assert x == 0 by {
                reveal prod();
            }
            assert x % p == 0;
        }else{
            assert x == prod(p,q) by {
                reveal prod();
            }
            prodSelfAnnihilation(p,q);
        }
    }

    ghost function Factors(x: nat): set<nat> 
        requires x > 0
    {
        set p: nat | 1 <=p <= x  && IsFactor(p, x)
    }

    ghost predicate Prime(p: nat) 
        requires p > 0
    {
        Factors(p) == {1, p}
    }

    opaque predicate is_prime(k: nat)    
    {
        k > 1 && forall d :: 2 <= d < k ==> k % d != 0
    }

    lemma PrimesEquivalent(k: nat)
        requires k > 0
        requires is_prime(k)
        ensures Prime(k)
    {
        reveal is_prime();
        var kfactors := Factors(k);
        assert prod(1, k) == k by {
            reveal prod();
        }
        assert prod(k, 1) == k by {
            reveal prod();
        }
        assert k > 1;
        assert 1 <= k;
        assert k <= k;
        // assert 1 * k == k;
        assert 1 in kfactors;
        assert k in kfactors;
        if x :| x in kfactors && x != 1 && x != k {
            assert x <= k;
            IsFactorDivides(x, k);
            assert false;
        }

    }

    opaque predicate hasDivisor(k: nat)
    {
        exists d: nat :: 2 <= d < k && k % d == 0
    }

    opaque predicate hasNoDivisorLessThan(k: nat, q: nat)
        requires 2 <= q <= k
    {
        forall d: nat :: 2 <= d < q < k ==> k % d != 0
    }

    lemma notPrimeHasDivisor(k: nat)
        requires k > 2
        requires !is_prime(k)
        ensures hasDivisor(k)
    {
        reveal is_prime();
        reveal hasDivisor();
    }
     
    lemma hasDivisorNotPrime(k: nat)
        requires k > 1
        requires hasDivisor(k)
        ensures !is_prime(k)
    {
        reveal is_prime();
        reveal hasDivisor();
    }

    predicate sievedPrimes(sieve: array<bool>, i: nat) 
        reads sieve
        requires 2 <= i < sieve.Length
    {
        (forall k: nat :: 0 <= k <= i ==> (sieve[k] ==> is_prime(k)) && (!sieve[k] ==> !is_prime(k)))
        && (forall k: nat :: 1 <= k < i && sieve[k] ==> forall j:nat :: (k*k <= j < sieve.Length) && (j % k == 0) ==> !sieve[j] && hasDivisor(j))
        && (forall j:nat :: (i <= j < sieve.Length) && hasNoDivisorLessThan(j, i) ==> sieve[j])
    }
    
    predicate allSievedPrimes(sieve: array<bool>) 
        reads sieve
    {
        forall k: nat :: 0 <= k < sieve.Length ==> (sieve[k] ==> is_prime(k)) && (!sieve[k] ==> !is_prime(k))
    }

    lemma SievedToQ(sieve: array<bool>, i: nat, n: nat)
        requires n > 2
        requires n+1 == sieve.Length
        requires 0 <= i < sieve.Length
        requires IsNatSqrt(i, n)
        requires sievedPrimes(sieve, i)
        ensures allSievedPrimes(sieve)
    {
        assert forall k: nat :: 0 <= k <= i ==> (sieve[k] ==> is_prime(k)) && (!sieve[k] ==> !is_prime(k));
        assert forall k: nat :: 1 <= k < i && sieve[k] ==> forall j:nat :: (k*k <= j < sieve.Length) && (j % k == 0) ==> !sieve[j] && hasDivisor(j);
        assert forall j:nat :: (i <= j < sieve.Length) && hasNoDivisorLessThan(j, i) ==> sieve[j];
        assert forall k: nat :: i < k < sieve.Length ==> (sieve[k] ==> is_prime(k)) && (!sieve[k] ==> !is_prime(k)) by {
            forall k:  nat | i < k < sieve.Length
                ensures (sieve[k] ==> is_prime(k)) && (!sieve[k] ==> !is_prime(k))
            {

                if !sieve[k] {
                    assert hasDivisor(k);
                    assert !is_prime(k);
                }else{
                    assert is_prime(k);

                }
            }
        }
    }


    method {:verify false} EratosthenesSieve(n: nat) returns (primes: set<nat>)        
        requires n > 2    
        //[1] i want to proof it:
        ensures forall k :: k in primes ==> is_prime(k)
        //[2] i want to proof it:
        // ensures forall k :: 2 <= k <= n && is_prime(k) ==> k in primes
    {
        var sieve: array<bool> := new bool[n+1];
        forall i:nat | 0 <= i < 2 { sieve[i] := false; }    
        forall i:nat | 2 <= i < n { sieve[i] := true; }    


        var i: nat := 2;
        var q := sqrt(n);
        assert q < n;
        assert forall i:nat :: 2 <= i < n ==> sieve[i] == true;
        assert sievedPrimes(sieve, 2) by {
        assert sieve[0] == false;
        assert sieve[1] == false;
        assert !is_prime(0) by {
            reveal is_prime();
        }
        assert !is_prime(1) by {
            reveal is_prime();
        }
        assert sieve[2] == true;
        assert is_prime(2) by {
            reveal is_prime();
        }
        assert forall k:nat :: 0 <= k <= 2 ==> (sieve[i] ==> is_prime(i)) && !sieve[i] ==> !is_prime(i) by {
            reveal is_prime();
        }

        // assert forall k:nat :: 0 <= k <= 2 ==> !sieve[i] ==> !is_prime(i) by {
        //     reveal is_prime();
        // }

        }
        // assume exists k: nat :: 2<= k < n && k*k < n && 3 <= k+1 < n && (k+1)*(k+1) >= n;
        // var k:nat :| 1<= k < n && prod(k,k) < n && 2<= k+1 < n && prod((k+1),(k+1)) >= n;
        while i < q
            invariant n + 1 == sieve.Length        
            // invariant 2 <= i <= k+1
            invariant 2 <= i <= q < n
            invariant 2 <= i < q ==> i*i < n
            invariant sievedPrimes(sieve, i)
            invariant i == q ==> i*i >= n
            // decreases n - i
        {
            if sieve[i] {            
                forall j:nat | (i * i <= j < n) && (j % i == 0) { sieve[i] := false; }    
                //[3] assertion might not hold        
                // assert forall j:nat :: (i * i <= j < n) && (j % i == 0) ==> sieve[j] == false;
            }
            i := i + 1;
            assume sievedPrimes(sieve, i);
        }
        assert sievedPrimes(sieve, i);
        // assert allSievedPrimes(sieve);
        primes := {}; 
        for i := 2 to n {
            if sieve[i] {
                assert i < sieve.Length;
                assert is_prime(i);
                primes := primes + {i};
            }
        }    
    }
}