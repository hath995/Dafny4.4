
module Analysis {
    /**type defs */
    type pos = x: nat | 1 <= x witness 1

    /** axioms */
    lemma CompletenessAxiomUpper(A: iset<real>, a: real)
        requires exists p: real :: p in A 
        requires upperBound(A, a)
        // ensures exists k: real :: leastUpperBound(A, k) && upperBound(A, k)
        ensures exists k: real :: sup(A, k)

    lemma CompletenessAxiomLower(A: iset<real>, a: real)
        requires exists p: real :: p in A 
        requires lowerBound(A, a)
        // ensures exists k: real :: greatestLeastBound(A, k) && lowerBound(A, k)
        ensures exists k: real :: inf(A, k)

    lemma MonotoneConvergenceThmInc(a_i: pos -> real)
        requires MonotonicIncreasingSequence(a_i)
        ensures (forall a: real :: !Limit(a_i, a)) || exists a: real :: sup(iset n: pos | true :: a_i(n), a) && Limit(a_i, a)


    lemma MonotoneConvergenceThmDec(a_i: pos -> real)
        requires MonotonicDecreasingSequence(a_i)
        ensures (forall a: real :: !Limit(a_i, a)) || exists a: real :: inf(iset n: pos | true :: a_i(n), a) && Limit(a_i, a)

    lemma WellOrderingPrinciple(s: iset<pos>)
        requires s != iset{}
        ensures exists min :: min in s && forall x | x in s && x != min :: min < x; 

    /** functions */
    function Range<T, U>(f: T -> U, A: set<T>): set<U> {
        set x | x in A :: f(x)
    }

    function sub(a: real, b: real): real {
        a - b
    }

    function add(a: real, b: real): real {
        a+b
    }

    function prod(a: real, b: real): real {
        a * b
    }

    function div(a: real, b: real): real 
        requires b != 0.0
    {
        a / b
    }

    function abs(a: real): real {
        if a >= 0.0 then a else -a
    }

    function SubSequenceOf(a_i: pos -> real, k_i: pos -> pos): pos -> real
        requires MonotonicIncreasingPos(k_i)
    {
        (n: pos) => a_i(k_i(n))
    }

    function addSequence(a_i: pos -> real, b_i: pos -> real): pos -> real {
        (n:pos) => a_i(n) + b_i(n)
    }

    function prodSequence(a_i: pos -> real, b_i: pos -> real): pos -> real {
        (n:pos) => prod(a_i(n) , b_i(n))
    }

    function subSequence(a_i: pos -> real, b_i: pos -> real): pos -> real {
        (n:pos) => a_i(n) - b_i(n)
    }

    function mulSequence(a_i: pos -> real, c: real): pos -> real {
        (n:pos) => prod(c, a_i(n))
    }

    function maxNat(a: nat, b: nat): nat {
        if a >= b then a else b
    }

    function maxReal(a: real, b: real): real {
        if a >= b then a else b
    }
    /** predicates */
    ghost predicate Injective<A(!new), B>(f: A -> B)
    {
        forall x, y :: x != y ==> f(x) != f(y)
    }

    ghost predicate isTotal<G(!new), B(!new)>(f:G -> B)
        reads f.reads
    {
        forall g:G :: f.requires(g)
    }

    ghost predicate Surjective<A(!new), B(!new)>(f: A -> B) 
        reads f.reads
        // requires isTotal(f)
    {
        forall b: B :: exists a: A :: f(a) == b 
    }

    ghost predicate Bijective<A(!new), B(!new)>(f: A -> B) 
    {
        Injective(f) && Surjective(f)
    }

    ghost predicate upperBound(A: iset<real>, a: real) {
        forall x :: x in A ==> x <= a    
    }

    ghost predicate lowerBound(A: iset<real>, b: real) {
        forall x :: x in A ==> x >= b
    }

    ghost predicate leastUpperBound(A: iset<real>, a: real) 
    {
        forall epsilon: real :: epsilon > 0.0 ==> !upperBound(A, sub(a, epsilon))  
    }

    ghost predicate greatestLeastBound(A: iset<real>, b: real) {
        forall epsilon: real :: epsilon > 0.0 ==> !lowerBound(A, add(b , epsilon))  
    }

    ghost predicate sup(A: iset<real>, a: real) {
        upperBound(A, a) && leastUpperBound(A, a)
    }

    ghost predicate inf(A: iset<real>, b: real) {
        lowerBound(A, b) && greatestLeastBound(A, b)
    }

    ghost predicate minimalElement(A: iset<real>, a: real) {
        a in A && lowerBound(A, a)
    }

    ghost predicate maximalElement(A: iset<real>, a: real) {
        a in A && upperBound(A, a)
    }

    predicate lessThanEqual(n: nat, x: real) {
        n as real <= x
    }
    
    predicate greaterThan(n: nat, x: real) {
        n as real > x
    }

    predicate lessThan(n: nat, x: real) {
        n as real < x
    }

    predicate positiveNat(x: nat) {
        x > 0
    }

    predicate positiveReal(x: real) {
        x > 0.0
    }

    predicate converges(a_i: pos -> real, n: pos, epsilon: real, a: real) {
        abs(a_i(n)-a) < epsilon
    }

    predicate CauchyCriterion(a_i: pos -> real, epsilon: real, m: pos, n: pos) {
        abs(a_i(m)-a_i(n)) < epsilon
    }

    ghost predicate isCauchy(a_i: pos -> real) {
        forall epsilon: real :: positiveReal(epsilon) ==> exists N: nat :: positiveNat(N) && forall n: pos,m:pos :: m > n > N ==> CauchyCriterion(a_i, epsilon, m, n)
    }

    ghost predicate MonotonicIncreasingPos(k_i: pos -> pos) {
        forall n,m :: n < m ==> k_i(n) < k_i(m)
    }

    ghost predicate MonotonicIncreasingSequence(a_i: pos -> real) {
        forall n,m :: n < m ==> a_i(n) <= a_i(m)
    }

    ghost predicate MonotonicDecreasingSequence(a_i: pos -> real) {
        forall n,m :: n < m ==> a_i(n) >= a_i(m)
    }

    ghost predicate Monotone(a_i: pos -> real) {
        MonotonicIncreasingSequence(a_i) || MonotonicDecreasingSequence(a_i)
    }
    ghost predicate Limit(a_i: pos -> real, a: real) {
        forall epsilon: real :: positiveReal(epsilon) ==> exists N: nat :: positiveNat(N) && forall n: pos :: n > N ==> converges(a_i, n, epsilon, a)
    }

    ghost predicate bounded(ss: iset<real>, L: real, U: real) {
        forall x :: x in ss ==> L <= x <= U
    }

    ghost predicate boundedSeq(a_i: pos -> real, L: real, U: real) {
        forall n:pos :: positiveNat(n) ==> L <= a_i(n) <= U
    }

    /** lemmas */
    lemma ArchProof(x: real, a: real, b: real)
        requires a > 0.0
        requires x == b/a
        ensures exists n: pos :: n as real > x
    {
        if x < 0.0 {
            assert 1 as real > x;
        }else{
            assert b >= 0.0;
            if forall n: pos :: n as real <= x {
                var naturals: iset<real> := iset ns: nat | lessThanEqual(ns, x) :: ns as real;
                // assert upperBound(naturals, x);
                if x <= 1.0 {
                    assert 2 as real > x;
                    assert false;
                }else{
                    assert lessThanEqual(1, x);
                    assert 1.0 in naturals;
                }
                CompletenessAxiomUpper(naturals, x);
                var alpha: real :| leastUpperBound(naturals, alpha as real) && upperBound(naturals, alpha as real); 
                var mp: nat := add(alpha , 1.0).Floor;
                assert lessThanEqual(mp, x);
                assert mp as real in naturals;
                assert upperBound(naturals, mp as real);

                assert false;
            }
        }
    }

    lemma ArchimedeanPrinciple(epsilon: real)
        requires epsilon > 0.0
        ensures exists n: pos :: 1.0 / (n as real) < epsilon
    {
        ArchProof(1.0 / epsilon, epsilon, 1.0);
        var n: pos :| n as real > 1.0 / epsilon;
        if epsilon >= 1.0 {
        }else{
            calc ==> {
                n as real > 1.0 / epsilon;
                {assert (n as real) *  epsilon > (1.0/epsilon)*epsilon;}
                (n as real) * epsilon > 1.0;
                epsilon > 1.0 / (n as real);
            }
        }
    }

    lemma TriangeInequality(a: real, b: real)
        ensures abs(a+b) <= abs(a) + abs(b)
    {
    }

    lemma SubSequenceOfMonotoneSequenceIsMonotone(a_i: pos -> real, k_i: pos -> pos, a: real)
        requires MonotonicIncreasingPos(k_i)
        requires Monotone(a_i)
        ensures Monotone(SubSequenceOf(a_i, k_i))
    {

    }

    lemma inequalitProduct(a: real, b: real, c: real)
        requires a < b
        requires c > 0.0
        ensures c*a < c*b
    {

    }


    lemma boundedEqual(a_i: pos -> real, a_range: iset<real>, L: real, U: real)
        requires a_range == iset n: pos | positiveNat(n) :: a_i(n)
        requires bounded(a_range, L, U)
        ensures boundedSeq(a_i, L, U)
    {
        forall n:pos | positiveNat(n)
            ensures L <= a_i(n) <= U
        {
            assert a_i(n) in a_range;
        }

    }

    lemma boundedEqualLeft(a_i: pos -> real, a_range: iset<real>, L: real, U: real)
        requires a_range == iset n: pos | positiveNat(n) :: a_i(n)
        requires boundedSeq(a_i, L, U)
        ensures bounded(a_range, L, U)
    {}

    lemma absProd(a: real, b: real)
        ensures abs(prod(a,b)) == prod(abs(a), abs(b))
    {}

    lemma prodLessThan(a: real, b: real, c: real)
        requires a > 0.0
        requires 0.0 <= b < c 
        ensures prod(a , b) < prod(a , c)
    {}

    lemma divSmaller(a: real, b: real)
        requires a >= 0.0
        requires b > a
        ensures div(a,b) < 1.0
    {
        var diff := b-a;
        assert a/(a+diff) < 1.0;
    }

    lemma divCommute(a: real, b: real, c: real)
        requires c != 0.0
        // ensures a * (b/c) == (a/c)*b
        ensures prod(a , div(b,c)) == prod(div(a,c),b)
    {
    }
}