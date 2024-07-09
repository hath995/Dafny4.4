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

    function Sqr(x: nat): nat {
        reveal prod();
        prod(x, x)
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
    lemma {:axiom} modMultiplication(aone: int, bone: int, atwo: int, btwo: int, n: int)
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
    
    lemma DivisorIsFactor(d: nat, n: nat)
        requires d >= 2
        requires n > 2
        requires n % d == 0
        ensures IsFactor(d, n)
    {
        var k := n/d;
        reveal prod();
        assert prod(d, k) == n;
    }

    ghost function Factors(x: nat): set<nat> 
        requires x > 0
    {
        set p: nat | 1 <=p <= x  && IsFactor(p, x)
    }

    ghost predicate Prime(p: nat) 
        requires p > 1
    {
        Factors(p) == {1, p}
    }

    opaque predicate is_prime(k: nat)    
    {
        k > 1 && forall d :: 2 <= d < k ==> k % d != 0
    }

    lemma PrimesEquivalent(k: nat)
        requires k > 1
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

    lemma PrimesEquivalentReverse(k: nat)
        requires k > 1
        requires Prime(k)
        ensures is_prime(k)
    {
        reveal is_prime();
        assert k > 1;
        assert forall d :: 2 <= d < k ==> k % d != 0 by {
            forall d | 2 <= d < k
                ensures k % d != 0
            {
                if k % d == 0 {
                    var n : nat := k / d;
                    reveal prod();
                    assert prod(d, n) == k;
                    assert IsFactor(d, k);
                    assert d in Factors(k);
                    assert false;
                }
            }
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

    lemma PrimeHasNoDivisor(k: nat)
        requires k > 2
        requires is_prime(k)
        ensures !hasDivisor(k)
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


    predicate multiplesOfKMarked(sieve: array<bool>, k: nat)
        requires 1 < k < sieve.Length
        reads sieve
    {
        forall j:nat :: (k*k <= j < sieve.Length) && (j % k == 0) ==> !sieve[j] && hasDivisor(j) && !hasNoDivisorLessThan(j, k+1)
    }

    predicate allMultiplesOfPrimesLessThanIAreMarked(sieve: array<bool>, i: nat)
        reads sieve
        requires 2 <= i < sieve.Length
    {
        forall k: nat :: 1 < k < i  ==> sieve[k] ==> multiplesOfKMarked(sieve, k)
    }

    predicate sievedPrimes(sieve: array<bool>, i: nat) 
        reads sieve
        requires 2 <= i < sieve.Length
    {
        (forall k: nat :: 0 <= k <= i ==> (sieve[k] ==> is_prime(k)) && (!sieve[k] ==> !is_prime(k)))
        && allMultiplesOfPrimesLessThanIAreMarked(sieve, i)
        && (forall j:nat :: (i <= j < sieve.Length) ==> (sieve[j] ==> hasNoDivisorLessThan(j, i)) && (!sieve[j] ==> hasDivisor(j)))
    }

    twostate predicate Preserved(sieve: array<bool>, i: nat) 
        requires 2 <= i < sieve.Length
        reads sieve
    {
        (i*i < sieve.Length ==> old(sieve[..i*i]) == sieve[..i*i])
        && (i*i >= sieve.Length ==> old(sieve[..]) == sieve[..])
    }

    twostate predicate PreservedRest(sieve: array<bool>, i: nat) 
        requires 2 <= i < sieve.Length
        reads sieve
    {
        (i*i < sieve.Length ==> (
            (forall j:nat :: (i * i <= j < sieve.Length) && (j % i != 0) ==> old(sieve[j]) == sieve[j]) && 
            (forall j:nat :: (i * i <= j < sieve.Length) && (j % i == 0) && old(!sieve[j]) ==> old(sieve[j]) == sieve[j]) &&
            (!sieve[i] ==> forall j:nat :: (0 <= j < sieve.Length) ==> old(sieve[j]) == sieve[j])))
        && (i*i >= sieve.Length ==> old(sieve[..]) == sieve[..])
    }

    twostate lemma iUnchanged(sieve: array<bool>, i: nat)
        requires 2 <=i <i+1 < sieve.Length
        requires Preserved(sieve, i)
        ensures sieve[i] == old(sieve[i])
    {
        if i*i < sieve.Length {
        assert i < i*i by {
            reveal prod();
        }
        assert old(sieve[i]) == sieve[i]; 
        } else{
        assert old(multiset(sieve[..])) == multiset(sieve[..]);
        assert old(sieve[i]) == sieve[i]; 
        }
    }

    twostate lemma PrimesStayMarked(sieve: array<bool>, i: nat)
        requires 2 <=i <i+1 < sieve.Length
        requires PreservedRest(sieve, i)
        requires Preserved(sieve, i)
        requires old(sievedPrimes(sieve, i))
        // requires old(allMultiplesOfPrimesLessThanIAreMarked(sieve, i))
        requires sieve[i] ==> forall j:nat :: (i * i <= j < sieve.Length) && (j % i == 0) ==> !sieve[j] && hasDivisor(j) && !hasNoDivisorLessThan(j, i+1)
        ensures allMultiplesOfPrimesLessThanIAreMarked(sieve, i+1)
    {
        if i*i < sieve.Length {
            assert i < i*i by {
                reveal prod();
            }
            assert (forall j:nat :: (i * i <= j < sieve.Length) && (j % i != 0) ==> old(sieve[j]) == sieve[j]);
            forall k: nat | 1 < k < i+1 
                ensures sieve[k] ==> multiplesOfKMarked(sieve, k)
            {
                if k == i {
                    if sieve[i] {
                    assert multiplesOfKMarked(sieve, i); 
                    }
                }else{
                    assert old(sieve[k]) == sieve[k];
                    if sieve[k] {
                        forall j: nat | k*k <= j < sieve.Length && (j % k == 0)
                            ensures !sieve[j] && hasDivisor(j) && !hasNoDivisorLessThan(j, k+1) 
                        {
                            if j < i*i {
                                assert old(sieve[j]) == sieve[j];
                            }else{
                                assert i * i <= j < sieve.Length;
                                if j % i != 0 {
                                    assert old(sieve[j]) == sieve[j];
                                    assert !sieve[j] && hasDivisor(j) && !hasNoDivisorLessThan(j, k+1);

                                }else{
                                    assert i*i <= j < sieve.Length && j % k ==  0;
                                    if old(!sieve[j]) {
                                        assert hasDivisor(j);
                                        assert !hasNoDivisorLessThan(j, k+1);
                                        var q :| 2 <= q < k+1 < j && j % q == 0;
                                        assert !sieve[j];

                                    }else{
                                        assert !sieve[j] && hasDivisor(j) && !hasNoDivisorLessThan(j, k+1);

                                    }
                                }
                            }
                        }
                        assert multiplesOfKMarked(sieve, k); 
                    } 
                }
            }

            assert allMultiplesOfPrimesLessThanIAreMarked(sieve, i+1);
        } else{
            assert allMultiplesOfPrimesLessThanIAreMarked(sieve, i+1);
        }
    }

    lemma primesMostlyOdd(x: nat)
        requires x > 2
        requires is_prime(x)
        ensures x % 2 == 1
    {
        if x % 2 == 0 {
            reveal is_prime();
        }
    }

    lemma mods(j: nat, i: nat, d: nat)
        requires i > 0
        requires d > 0
        requires i % d == 0
        requires j % i == 0
        ensures j % d == 0 
    {
        var s: nat := j / i;
        assert s * i ==j;
        var t: nat := i / d;
        assert t * d == i;
        calc {
            j;
            s*i;
            s*t*d;
        }
        prodSelfAnnihilation(d, s*t);
        reveal prod();
        assert j % d == 0;
    }

    lemma mods2(j: nat, i: nat, p: nat)
        requires i > 0 && p > 0
        requires j % i == 0
        requires j == prod(i, p)
        ensures j % p == 0
    {
        reveal prod();
        prodSelfAnnihilation(p, i);
       
    }

    predicate multiplesOfINotPrime(sieve: array<bool>, i: nat) 
        requires 2 <=i  < sieve.Length
        reads sieve
    {
        forall j:nat :: (i * i <= j < sieve.Length) && (j % i == 0) ==> sieve[j] == false
    }

    twostate lemma SievedContinue(sieve: array<bool>, i: nat, q: nat, n: nat)
        requires n > 2
        requires sieve.Length == n+1
        requires IsNatSqrt(q, n)
        requires i <= q+1
        requires 2 <=i <i+1 < sieve.Length
        requires old(sievedPrimes(sieve, i))
        requires Preserved(sieve, i)
        requires PreservedRest(sieve, i)
        requires sieve[i] ==> forall j:nat :: (i * i <= j < sieve.Length) && (j % i == 0) ==> !sieve[j] && hasDivisor(j) && !hasNoDivisorLessThan(j, i+1)
        ensures sievedPrimes(sieve, i+1)
    {
        PrimesStayMarked(sieve, i);
        if sieve[i] {
            // assert i <= i < sieve.Length;
            assert hasNoDivisorLessThan(i,i);
            assert is_prime(i);
            assert (forall k: nat :: 0 <= k <= i+1 ==> (sieve[k] ==> is_prime(k)) && (!sieve[k] ==> !is_prime(k))) by {
                assert (forall k: nat :: 0 <= k <= i ==> (sieve[k] ==> is_prime(k)) && (!sieve[k] ==> !is_prime(k)));
                assert (sieve[i+1] ==> is_prime(i+1)) && (!sieve[i+1] ==> !is_prime(i+1)) by {
                    assert sieve[2] by {
                        reveal is_prime();
                        assert is_prime(2);
                    }
                    assert sieve[3] by {
                        reveal is_prime();
                        assert is_prime(3);
                        PrimeHasNoDivisor(3);
                    }
                    if i == 2 {
                        assert is_prime(3) by {
                            reveal is_prime();
                        }
                        assert (sieve[i+1] ==> is_prime(i+1)) && (!sieve[i+1] ==> !is_prime(i+1));
                    }else{
                        assert i >= 3;
                        primesMostlyOdd(i);
                        assert (i+1) % 2 == 0;
                        assert !is_prime(i+1) by {
                            reveal is_prime();
                        }
                        assert !sieve[i+1] by {
                            assert old(sieve[i+1]) == sieve[i+1];
                            assert 1 <= 2 < i;
                        }
                        assert (sieve[i+1] ==> is_prime(i+1)) && (!sieve[i+1] ==> !is_prime(i+1));
                    }
                }
                // unless i == 2 then if i is prime then i+1 is even ==> !is_prime(i+1)
                // 2*2 <= j < sieve.Length && (i+1)%2 == 0 ==> !sieve[i+1] && hasDivisor(i+1)
            }
            assert allMultiplesOfPrimesLessThanIAreMarked(sieve, i);
            assert (forall j:nat :: (i+1 <= j < sieve.Length) ==> (sieve[j] ==> hasNoDivisorLessThan(j, i+1)) && (!sieve[j] ==> hasDivisor(j))) by {
                forall j: nat | i+1 <= j < sieve.Length
                    ensures (sieve[j] ==> hasNoDivisorLessThan(j, i+1)) && (!sieve[j] ==> hasDivisor(j))
                {
                    if sieve[j] {
                        assert old(sieve[j]) == sieve[j];
                        assert hasNoDivisorLessThan(j, i);
                        assert j % i != 0 by {
                            if j % i == 0 {
                                if j < i * i {
                                    var p: nat := j / i;
                                    assert j == i * p;
                                    assert j == prod(i, p) by {
                                        reveal prod();
                                    }
                                    assert p != 0;
                                    assert p < i by {
                                        if p >= i {
                                            var diff:nat := p - i;
                                            assert p == diff + i;
                                            calc {
                                                p * i;
                                                (diff+i)*i;
                                                diff*i + i*i;
                                            }
                                            assert p*i - i*i == diff*i;
                                            assert diff*i >= 0;
                                            assert p * i >= i *i;
                                            assert false;
                                        }
                                    }
                                    mods2(j, i, p);
                                    assert j % p == 0;
                                    reveal hasNoDivisorLessThan();

                                }
                                assert false;
                            }
                        }
                        assert hasNoDivisorLessThan(j, i+1) by {
                            reveal hasNoDivisorLessThan();
                        }
                    }else{

                    }
                }
            }
            assert sievedPrimes(sieve, i+1);
        }else{
            assert !is_prime(i);
            assert hasDivisor(i);
            assert (forall k: nat :: 0 <= k <= i+1 ==> (sieve[k] ==> is_prime(k)) && (!sieve[k] ==> !is_prime(k))) by {
                assert (forall k: nat :: 0 <= k <= i ==> (sieve[k] ==> is_prime(k)) && (!sieve[k] ==> !is_prime(k)));
                assert (sieve[i+1] ==> is_prime(i+1)) && (!sieve[i+1] ==> !is_prime(i+1)) by {
                    assert sieve[2] by {
                        reveal is_prime();
                        assert is_prime(2);
                    }
                    assert sieve[3] by {
                        reveal is_prime();
                        assert is_prime(3);
                        PrimeHasNoDivisor(3);
                    }
                    assert i > 3;
                    if sieve[i+1] {
                        assert hasNoDivisorLessThan(i+1, i);
                        noDivisorsUpToK(i+1);
                    }else{
                        assert hasDivisor(i+1);
                        hasDivisorNotPrime(i+1);

                    }
                    assert (sieve[i+1] ==> is_prime(i+1)) && (!sieve[i+1] ==> !is_prime(i+1));
                }

            }
            assert (forall j:nat :: (i+1 <= j < sieve.Length) ==> (sieve[j] ==> hasNoDivisorLessThan(j, i+1)) && (!sieve[j] ==> hasDivisor(j))) by {
                forall j: nat | i+1 <= j < sieve.Length
                    ensures (sieve[j] ==> hasNoDivisorLessThan(j, i+1)) && (!sieve[j] ==> hasDivisor(j))
                {
                    if i * i < sieve.Length {
                        assert !sieve[i];
                        assert 0 <= j < sieve.Length;
                        assert old(sieve[j]) == sieve[j];
                        if sieve[j] {
                            assert hasNoDivisorLessThan(j, i);
                            assert j % i != 0 by {
                                if j % i == 0 {
                                    assert !is_prime(i);
                                    assert i != 2 by {
                                        reveal is_prime();
                                        assert is_prime(2);
                                    }
                                    notPrimeHasDivisor(i);
                                    reveal hasDivisor();
                                    var d: nat :| 2 <= d < i && i % d == 0; 
                                        reveal hasNoDivisorLessThan();
                                    assert 2 <= d < i < j;
                                    mods(j, i, d);
                                    assert j % d == 0;
                                
                                    assert false;
                                }
                            }
                            assert hasNoDivisorLessThan(j, i+1) by {
                                reveal hasNoDivisorLessThan();
                            }
                        }else {
                            assert hasDivisor(j);
                        }

                    }else{
                        assert old(sieve[j]) == sieve[j];
                        if sieve[j] {
                            assert hasNoDivisorLessThan(j, i);
                            assert j % i != 0 by {
                                if j % i == 0 {
                                    assert !is_prime(i);
                                    assert i != 2 by {
                                        reveal is_prime();
                                        assert is_prime(2);
                                    }
                                    notPrimeHasDivisor(i);
                                    reveal hasDivisor();
                                    var d: nat :| 2 <= d < i && i % d == 0; 
                                        reveal hasNoDivisorLessThan();
                                    assert 2 <= d < i < j;
                                    mods(j, i, d);
                                    assert j % d == 0;
                                
                                    assert false;
                                }
                            }
                            assert hasNoDivisorLessThan(j, i+1) by {
                                reveal hasNoDivisorLessThan();
                            }
                        }else{
                            assert hasDivisor(j);
                        }
                    }
                }
            }
            assert sievedPrimes(sieve, i+1);
        }
    }
    
    predicate allSievedPrimes(sieve: array<bool>) 
        reads sieve
    {
        forall k: nat :: 0 <= k < sieve.Length ==> (sieve[k] ==> is_prime(k)) && (!sieve[k] ==> !is_prime(k))
    }

    lemma factorIsLessThan(a: nat, b: nat, c: nat)
        requires a > 1
        requires b > 1
        requires prod(a, b) == c
        ensures a < c
        ensures b < c
    {
        reveal prod();
    }

    lemma {:vcs_split_on_every_assert} NonPrimeHasFactorLessThanRoot(k: nat, i: nat)
        requires k > 2
        requires i < k
        requires !is_prime(k)
        requires IsNatSqrt(i, k)
        ensures exists d :: d in Factors(k) && 2 <= d <= i
    {
        notPrimeHasDivisor(k);
        reveal hasDivisor();
        var d :|  2 <= d < k && k % d == 0;
        DivisorIsFactor(d, k);
        assert d in Factors(k);
        assert IsFactor(d, k);
        assert exists d :: d in Factors(k) && 2 <= d <= i < k by {
            if !(exists d :: d in Factors(k) && 2 <= d <= i < k) {
                var nd: nat :| prod(d, nd) == k;
                assert nd != 0 by {
                    assert k != 0;
                    reveal prod();
                }
                assert nd != 1 by {
                    reveal prod();
                }
                assert IsFactor(nd, k) by {
                    reveal prod();
                    assert d * nd == k;
                    assert prod(nd, d) == k;
                    assert nd * d == k;
                }
                assert nd in Factors(k) by {
                    factorIsLessThan(d, nd, k);
                    assert nd < k;
                }
                assert nd > i;

                assert prod(d,nd) != k by {
                    reveal prod();
                    var d' := d-i;
                    var dd' := nd-i;
                    assert d' > 0;
                    assert dd' > 0;
                    calc {
                        d * nd;
                        (i+d')*(i+dd');
                    }
                }
                assert false;   
            }
        }
    }
    
    lemma rootPlusOne(k: nat, kroot: nat)
        requires 2 <=kroot
        requires 3 < k
        requires IsNatSqrt(kroot, k)
        ensures kroot+1 < k
    {
        assert (kroot-1)*(kroot-1) < k;
        assert kroot*kroot >= k;
        if kroot + 1 == k {
            calc{
                (kroot-1)*(kroot-1);
                kroot*kroot -2*kroot + 1;
            }
            calc{
                k*k;
                (kroot+1)*(kroot+1);
                kroot*kroot + 2*kroot+1;
            }
            assert kroot*kroot + 2*kroot+1 == k*k;
            assert kroot*kroot - (kroot*kroot -2*kroot + 1) == 2*kroot-1;
            assert 2*kroot-1 >= 3;
            assert 1 < 3;
            assert false;
        }else if kroot + 1 > k {
            assert false;

        }
    }

    lemma noDivisorsUpToK(k: nat)
        requires k > 3
        requires hasNoDivisorLessThan(k, k-1)
        ensures is_prime(k)
    {
        if !is_prime(k) {
            NatSqrtExist(k);
            var kroot: nat :| IsNatSqrt(kroot, k);
            assert kroot < k;
            assert kroot >= 2;
            assert kroot <= k-2 < k-1 by {
                assert (kroot-1)*(kroot-1) < k;
                assert kroot*kroot >= k;

            }
            NonPrimeHasFactorLessThanRoot(k, kroot);
            var d :| d in Factors(k) && 2 <= d <= kroot;
            IsFactorDivides(d, k);
            assert k % d == 0;
            reveal hasNoDivisorLessThan();
            assert false;
        }
    }

    lemma noDivisorsIsPrime(k: nat, n: nat, i: nat)
        requires 2 <= i+1 < k <= n
        requires IsNatSqrt(i, n)
        requires hasNoDivisorLessThan(k, i+1)
        ensures is_prime(k)
    {
        if k == n {
            if !is_prime(k) {
                NonPrimeHasFactorLessThanRoot(k, i);
                var d :| d in Factors(k) && 2 <= d <= i < k;
                IsFactorDivides(d, k);
                reveal hasNoDivisorLessThan();
                reveal is_prime();
                assert false;
            }
        }else{
            if !is_prime(k) {
                NatSqrtExist(k);
                var kroot: nat :| IsNatSqrt(kroot, k);
                sqrtRelation(k,n,kroot, i);
                assert kroot <= i < i+1;
                NonPrimeHasFactorLessThanRoot(k, kroot);
                var d :| d in Factors(k) && 2 <= d <= kroot;
                IsFactorDivides(d, k);
                assert k % d == 0;
                reveal hasNoDivisorLessThan();
                assert 2 < i < i+1;
                assert k % i != 0;
                assert false;
            }
        }
    }

    lemma SievedToQ(sieve: array<bool>, i: nat, n: nat)
        requires n > 2
        requires n+1 == sieve.Length
        requires 0 <= i < sieve.Length
        requires IsNatSqrt(i, n)
        requires sievedPrimes(sieve, i+1)
        ensures allSievedPrimes(sieve)
    {
        assert forall k: nat :: i+1 < k < sieve.Length ==> (sieve[k] ==> is_prime(k)) && (!sieve[k] ==> !is_prime(k)) by {
            forall k:  nat | i+1 < k < sieve.Length
                ensures (sieve[k] ==> is_prime(k)) && (!sieve[k] ==> !is_prime(k))
            {
                if !sieve[k] {
                    assert !hasNoDivisorLessThan(k, i) ==> !sieve[k];
                    assert hasDivisor(k);
                    hasDivisorNotPrime(k);
                    assert !is_prime(k);
                }else{
                    assert hasNoDivisorLessThan(k, i+1);
                    assert k <= n;
                    noDivisorsIsPrime(k,n,i);
                    assert is_prime(k);
                }
            }
        }
    }
    
    twostate lemma oldMultisets(sieve: array<bool>, l: nat)
        requires l <= sieve.Length
        requires forall j :: 0 <= j < l <= sieve.Length ==> old(sieve[j]) == sieve[j]
        ensures multiset(old(sieve[..l])) == multiset(sieve[..l])
    {
        if l == 0 {
        }else{
            assert l-1 >= 0;
            oldMultisets(sieve, l-1);
        }
    }

    twostate lemma oldMultisetsFull(sieve: array<bool>)
        requires forall j :: 0 <= j <  sieve.Length ==> old(sieve[j]) == sieve[j]
        ensures multiset(old(sieve[..])) == multiset(sieve[..])
    {
        oldMultisets(sieve, sieve.Length);
        assert sieve[..sieve.Length] == sieve[..];
        assert old(sieve[..sieve.Length]) == old(sieve[..]);
    }

    lemma SieveTo2(sieve: array<bool>, n: nat, i: nat)
        requires n > 3
        requires sieve.Length == n+1
        requires i == 2
        requires forall i:nat :: 0 <= i < 2 ==> !sieve[i]
        requires forall i:nat :: 2 <= i < sieve.Length ==> sieve[i]
        ensures sievedPrimes(sieve, 2)
    {
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

            assert (forall k: nat :: 1 <= k < 2  ==> sieve[k] ==> forall j:nat :: (k*k <= j < sieve.Length) && (j % k == 0) ==> !sieve[j] && hasDivisor(j));
            assert forall j:nat :: (2 <= j < sieve.Length) ==> (sieve[j] ==> hasNoDivisorLessThan(j, 2)) && (!sieve[j] ==> hasDivisor(j)) by {
                assert forall j:nat :: 2 <= j < sieve.Length ==> sieve[j];
                forall j: nat | 2 <= j < sieve.Length
                ensures (sieve[j] ==> hasNoDivisorLessThan(j, 2)) && (!sieve[j] ==> hasDivisor(j))
                {
                    assert sieve[j];
                    reveal hasNoDivisorLessThan();
                    assert hasNoDivisorLessThan(j, 2);
                }
            }
        }
    }


    method EratosthenesSieve(n: nat) returns (primes: set<nat>)        
        requires n > 3    
        ensures forall k :: k in primes ==> is_prime(k)
        ensures forall k :: 2 <= k <= n && is_prime(k) ==> k in primes
    {
        var sieve: array<bool> := new bool[n+1];
        forall i:nat | 0 <= i < 2 { sieve[i] := false; }    
        forall i:nat | 2 <= i < sieve.Length { sieve[i] := true; }    

        var i: nat := 2;
        var q := sqrt(n);
        assert q < n;
        assert forall i:nat :: 2 <= i < n ==> sieve[i] == true;
        SieveTo2(sieve, n, i);
        rootPlusOne(n, q);
        while i <= q
            invariant allocated(sieve)
            invariant n + 1 == sieve.Length        
            invariant 2 <= i <= q+1 < n
            invariant 2 <= i < q ==> i*i < n
            invariant sievedPrimes(sieve, i)
            // invariant forall k :: 2 <= k <=i && is_prime(k) ==> sieve[k]
            // invariant forall k :: 2 <= k <=i*i < sieve.Length && is_prime(k) ==> sieve[k]
            invariant i == q ==> i*i >= n
        {
            label S:
            if sieve[i] {            
                forall j:nat | (i * i <= j < sieve.Length) && (j % i == 0) { sieve[j] := false; }    
                assert forall j:nat :: (i * i <= j < sieve.Length) && (j % i == 0) ==> !sieve[j] && hasDivisor(j) && !hasNoDivisorLessThan(j, i+1) by {
                    forall j:nat | (i * i <= j < sieve.Length) && (j % i == 0) 
                        ensures !sieve[j] && hasDivisor(j) && !hasNoDivisorLessThan(j, i+1)
                    {
                        reveal hasDivisor();
                        reveal hasNoDivisorLessThan();
                        assert 2 <= i < j;
                        assert j % i == 0;
                    }
                }
                assert PreservedRest@S(sieve, i);
            }else{
                assert PreservedRest@S(sieve, i);
            }
            assert Preserved@S(sieve, i);
            SievedContinue@S(sieve, i, q, n);
            i := i + 1;
        }
        // assert sievedPrimes(sieve, q+1);
        SievedToQ(sieve, q, n);
        assume forall k :: 2 <= k <= n && is_prime(k) ==> sieve[k]; //@TODO: 
        primes := {}; 
        var z := 1;
        while z <= n
            invariant 1 <= z <= n+1
            invariant forall x :: x in primes ==> is_prime(x)
            invariant forall k :: 1 <= k < z && sieve[k] ==> k in primes
        {
            if sieve[z] {
                assert z < sieve.Length;
                assert is_prime(z);
                primes := primes + {z};
            }
            z := z + 1;
        }    
        assert forall k :: 2 <= k <= n && sieve[k] ==> k in primes;
    }

    method Main() {
        var result := EratosthenesSieve(100);
        print "RES: \n";
        print result;
        print "\n";
    }
}