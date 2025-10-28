//https://interjectedfuture.com/the-best-way-to-learn-might-be-starting-at-the-end/
module ZSets {
    type ZSet<!A> = A -> int

    ghost predicate ZEqual<A(!new)>(left: ZSet<A>, right: ZSet<A>) {
        forall a: A :: true ==> left(a) == right(a)
    }

    ghost predicate ValidZSet<A(!new)>(zs: ZSet<A>) {
        exists im: imap<A, int> :: (forall a: A :: true ==> a in im && im[a] == zs(a))
    }

    function Add<A(!new)>(zs1: ZSet<A>, zs2: ZSet<A>): ZSet<A> {
        (x: A) => zs1(x) + zs2(x)
    }

    lemma LemmaValidAdd<A(!new)>(zs1: ZSet<A>, zs2: ZSet<A>)
        requires ValidZSet(zs1)
        requires ValidZSet(zs2)
        ensures ValidZSet(Add(zs1, zs2))
    {
        var im := imap a: A | true :: zs1(a) + zs2(a);
    }

    function Neg<A(!new)>(zs1: ZSet<A>): ZSet<A> {
        (x: A) => -zs1(x)
    }

    function singleton<A(!new,==)>(a: A, n: int): ZSet<A> {
        (x: A) => if x == a then n else 0
    }

    lemma LemmaValidNeg<A(!new)>(zs1: ZSet<A>)
        requires ValidZSet(zs1)
        ensures ValidZSet(Neg(zs1))
    {
        var im := imap a: A | true :: -zs1(a);
    }

    function Zero<A(!new)>(a: A): int {
        0
    }


    lemma LemmaValidZero<A(!new)>()
        ensures ValidZSet(Zero<A>)
    {
        var im := imap a: A | true :: 0;
        // assert forall a: A :: true ==> Zero<A>(a) == 0;
    }

    lemma LemmaAdditveInverse<A(!new)>(zs: ZSet<A>)
        requires ValidZSet(zs)
        ensures ZEqual(Add(zs, Neg(zs)), Zero<A>)
    {
    }

    lemma LemmaAddAssociative<A(!new)>(zs1: ZSet<A>, zs2: ZSet<A>, zs3: ZSet<A>)
        ensures ZEqual(Add(Add(zs1, zs2), zs3), Add(zs1, Add(zs2, zs3)))
    {
        // Associativity follows from the associativity of integer addition
        // For any element a: Add(Add(zs1, zs2), zs3)(a) = (zs1(a) + zs2(a)) + zs3(a)
        // And Add(zs1, Add(zs2, zs3))(a) = zs1(a) + (zs2(a) + zs3(a))
        // Since integer addition is associative, these are equal
    }

    lemma LemmaAddCommutative<A(!new)>(zs1: ZSet<A>, zs2: ZSet<A>)
        ensures ZEqual(Add(zs1, zs2), Add(zs2, zs1))
    {
        // Commutativity follows from the commutativity of integer addition
        // For any element a: Add(zs1, zs2)(a) = zs1(a) + zs2(a)
        // And Add(zs2, zs1)(a) = zs2(a) + zs1(a)
        // Since integer addition is commutative, these are equal
    }

    lemma LemmaAddZeroIdentity<A(!new)>(zs1: ZSet<A>)
        ensures ZEqual(Add(zs1, Zero<A>), zs1)
    {
        // Zero is the additive identity
        // For any element a: Add(zs1, Zero<A>)(a) = zs1(a) + Zero<A>(a) = zs1(a) + 0 = zs1(a)
        // Since adding zero to any integer gives the same integer
    }

}