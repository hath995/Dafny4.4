include "../lib/gcd.dfy"



module Artin {
    import Math

    function sub(x: int, y: int): int {
        x - y
    }

    lemma prodDistributesSub(a: int, b: int, c: int)
        ensures  Math.prod(a,b) + Math.prod(a,sub(c,b)) == Math.prod(a, c)
    {
        reveal Math.prod();
    }

    lemma prodDistributesMinus(a: int, b: int, c: int)
        ensures Math.prod(a, b - c) == Math.prod(a,b) - Math.prod(a,c)
    {
        reveal Math.prod();
    }

    lemma prodNegative(a: int, b: int)
        ensures -Math.prod(a,b) == Math.prod(-1, Math.prod(a,b))
    {
        reveal Math.prod();
    }

    lemma prodZero(a: int, b: int)
        requires b == 0
        ensures Math.prod(a, b) == 0
    {
        reveal Math.prod();
    }
    //!A signifies type invariance
    datatype Group<!A> = Group(elements: set<A>, identity: A, compose: (A,A) -> A, inverse: (A) -> A)

    opaque ghost predicate isIdentity<A(!new)>(g: Group<A>) {
        forall a :: inGroup(g,a) ==> g.compose(a,g.identity) == a && g.compose(g.identity, a) == a
    }

    lemma GroupIdentity<A(!new)>(g: Group<A>, a: A) 
        requires ValidGroup(g)
        requires inGroup(g, a)
        ensures g.compose(a,g.identity) == a && g.compose(g.identity, a) == a
    {
       reveal ValidGroup();
       reveal isIdentity(); 
    }
    

    opaque ghost predicate closedComposition<A(!new)>(g: Group<A>) {
        // forall x,y :: x in g.elements && y in g.elements ==> g.compose(x,y) in g.elements
        forall x: A, y: A :: inGroup(g,x) && inGroup(g,y) ==> inGroup(g, g.compose(x,y))
    }

    lemma GroupClosedComposition<A>(g: Group<A>, a: A, b: A)
        requires inGroup(g, a)
        requires inGroup(g, b)
        ensures inGroup(g, g.compose(a, b))

    ghost predicate associativeComposition<A(!new)>(g: Group<A>) {
        forall a,b,c :: inGroup(g, a) && inGroup(g, a) && inGroup(g,a) ==> g.compose(g.compose(a,b),c) == g.compose(a, g.compose(b,c))
    }

    lemma GroupAssociativeComposition<A>(g: Group<A>, a: A, b: A, c: A)
        requires inGroup(g, a)
        requires inGroup(g, b)
        requires inGroup(g, c)
        ensures g.compose(g.compose(a,b),c) == g.compose(a, g.compose(b,c))


    ghost predicate commutativeComposition<A(!new)>(g: Group<A>) {
        forall a,b :: inGroup(g, a) && inGroup(g, a) ==> g.compose(a,b) == g.compose(b,a)
    }

    //problematic, aka recursive trigger, it generates new patterns that match the trigger
    ghost predicate containsInverses<A(!new)>(g: Group<A>) {
        forall x :: inGroup(g, x) ==> exists xbar :: inGroup(g, xbar) && g.compose(x,xbar) == g.identity
    }

    lemma GroupContainsInverse<A>(g: Group<A>, x: A)
        requires inGroup(g, x)
        ensures inGroup(g, g.inverse(x))

    predicate PleaseInstantiateMe<A>(x: A) {
        true
    }

    //no longer blocks apowAddition, but doesn't help groupCompositionInverse
    // predicate containsInverses<A>(g: Group<A>) {
    //   forall x {:trigger PleaseInstantiateMe(x)} :: 
    //     PleaseInstantiateMe(x) && x in g.elements ==> 
    //     exists xbar :: 
    //       xbar in g.elements && g.compose(x,xbar) == g.identity
    // }
    ghost predicate closedInverse<A(!new)>(g: Group<A>) {
        // forall x {:trigger g.inverse(x)} :: x in g.elements ==> g.inverse(x) in g.elements
        forall x {:trigger g.inverse(x)} :: inGroup(g,x) ==> inGroup(g,g.inverse(x))
    }

    ghost predicate isInverse<A(!new)>(g: Group<A>) {
        // forall x {:trigger g.inverse(x)} :: x in g.elements ==> g.compose(x,g.inverse(x)) == g.identity && g.compose(g.inverse(x),x) == g.identity
        forall x {:trigger g.inverse(x)} :: inGroup(g,x) ==> g.compose(x,g.inverse(x)) == g.identity && g.compose(g.inverse(x),x) == g.identity
    }
    
    lemma GroupInverse<A>(g: Group<A>, x: A)
        requires inGroup(g, x)
        ensures g.compose(x,g.inverse(x)) == g.identity && g.compose(g.inverse(x),x) == g.identity


    lemma areInverses<A(!new)>(g: Group<A>, a: A,  b: A)
        requires ValidGroup(g)
        requires a in g.elements && b in g.elements
        requires inGroup(g,a) && inGroup(g,b)
        requires g.compose(a, b) == g.identity && g.compose(b,a) == g.identity
        ensures g.inverse(a) == b && g.inverse(b) == a
    {
        var x := g.inverse(b);
        GroupInverse(g, b);
        GroupInverse(g, a);
        GroupContainsInverse(g, b);
        GroupAssociativeComposition(g, a, b, x);
        GroupClosedComposition(g, a, b);
        GroupIdentity(g, x);
        GroupIdentity(g, a);
        GroupIdentity(g, b);
        calc {
            x;
            g.compose(g.identity, x);
            g.compose(g.compose(a,b), x);
            g.compose(a,g.compose(b, x));
            g.compose(a, g.identity);
            a;
        }

        var y := g.inverse(a);
        GroupContainsInverse(g, a);
        GroupIdentity(g, y);
        GroupAssociativeComposition(g, y, a, b);
        calc {
            y;
            g.compose(y, g.identity);
            g.compose(y, g.compose(a,b));
            g.compose(g.compose(y, a),b);
            g.compose(g.identity, b);
            b;
        }
    }

    opaque ghost predicate ValidGroup<A(!new)>(g: Group<A>) {
        // g.identity in g.elements &&
        inGroup(g, g.identity) &&
        isIdentity(g) &&
        closedComposition(g) &&
        associativeComposition(g) &&
        closedInverse(g) &&
        isInverse(g)
        // containsInverses(g)
    }

    ghost predicate ValidGroupAxiom<A(!new)>(g: Group<A>) {
        // g.identity in g.elements &&
        inGroup(g, g.identity)
        //isIdentity(g) &&
        //closedComposition(g) &&
        //associativeComposition(g) &&
        //closedInverse(g) &&
        //isInverse(g)
        // containsInverses(g)
    }

    lemma VGAIdentity<A(!new)>(g: Group<A>)
        requires ValidGroup(g)
        ensures isIdentity(g)
    {
        reveal ValidGroup();
    }

    ghost predicate ValidSubGroup<A(!new)>(g: Group<A>, h: Group<A>) {
        h.elements <= g.elements &&
        g.identity in h.elements &&
        g.identity == h.identity &&
        g.inverse == h.inverse &&
        g.compose == h.compose //&&
        //closedComposition(h) //&&
        // containsInverses(h)
    }

    ghost predicate AbelianGroup<A(!new)>(g: Group<A>) {
        ValidGroup(g) && commutativeComposition(g)
    }

    lemma {:verify true} groupCompositionInverse<A(!new)>(g: Group<A>, a: A, b: A, abar: A, bbar: A, abbar: A)
        requires ValidGroup(g)
        requires inGroup(g, a)
        requires inGroup(g,b)
        requires g.inverse(a) == abar
        requires g.inverse(b) == bbar
        requires g.inverse(g.compose(a,b)) == abbar
        ensures abbar == g.compose(bbar, abar)
    {
        GroupContainsInverse(g, a);
        GroupContainsInverse(g, b);
        GroupInverse(g, a);
        GroupInverse(g, b);
        GroupIdentity(g, abar);
        GroupIdentity(g, b);
        GroupClosedComposition(g, bbar, abar);
        GroupClosedComposition(g, a, b);
        GroupContainsInverse(g, g.compose(a,b));
        GroupInverse(g, a);
        GroupAssociativeComposition(g, b, bbar, abar );
        GroupAssociativeComposition(g, a, b, g.compose(bbar, abar));
        calc {
            g.compose(g.compose(a, b), g.compose(bbar, abar));
            g.compose(a, g.compose(b, g.compose(bbar, abar)));
            g.compose(a, g.compose(g.compose(b, bbar),abar));
            ==
            g.compose(a, g.compose(g.identity,abar));
            ==
            g.compose(a, abar);
            ==
            g.identity;
        }

        // GroupAssociativeComposition(g, b, bbar, abar );
        GroupAssociativeComposition(g, g.compose(bbar, abar), a,b);
        GroupAssociativeComposition(g, bbar, abar, g.compose(a,b));
        GroupAssociativeComposition(g, abar, a, b);
        calc {
            g.compose(g.compose(bbar, abar), g.compose(a, b));
            g.compose(bbar, g.compose(abar, g.compose(a, b)));
            g.compose(bbar, g.compose(abar, g.compose(a, b)));
            g.compose(bbar, g.compose(g.compose(abar, a), b));
            g.compose(bbar, g.compose(g.identity, b));
            g.compose(bbar, b);
            g.identity;
        }
        areInverses(g, g.compose(a,b), g.compose(bbar, abar));
    }
    /*
function realExp(r: real, e: int): real decreases if e > 0 then e else -e {
  if e == 0 then r
  else if e < 0 then realExp(r/10.0, e+1)
  else realExp(r*10.0, e-1)
}
    */

    function npow<A>(g: Group, elem: A, n: nat): A
        ensures n == 0 ==> npow(g,elem,n) == g.identity
    {
        if n == 0 then g.identity else g.compose(elem, apow(g, elem, n-1)) 
    }
    lemma npowPos<A(!new)>(g: Group, elem: A, n: int)
        requires n > 0
        requires ValidGroup(g)
        requires inGroup(g, elem)
        ensures npow(g,elem,n) == g.compose(npow(g, elem, n-1), elem)
    {
        GroupIdentity(g, elem);
        if n == 1 {
            calc {
                npow(g,elem,n);
                g.compose(elem, npow(g, elem, 0));
                g.compose(elem, g.identity);
                elem;
            }
            calc {
                g.compose(npow(g, elem, n-1), elem);
            }

        }else{
            npowPos(g, elem, n-1);
            assume npow(g, elem, n-2) in g.elements;
            GroupAssociativeComposition(g, elem, npow(g, elem, n-2), elem);
            calc {
                npow(g,elem,n);
                g.compose(elem, npow(g, elem, n-1));
                g.compose(elem, g.compose(npow(g, elem, n-2), elem));
                g.compose(g.compose(elem,npow(g, elem, n-2)), elem);
                g.compose(npow(g, elem, n-1), elem);
            }
        }
    }

    function zpow<A>(g: Group, elem: A, z: int): A
    {
        if z >= 0 then npow(g, elem, z) else g.inverse(npow(g, elem, -z))
    }

    //apow is short for abstract power
    function apow<A>(g: Group, elem: A, n: int): A
        decreases if n > 0 then n else -n
        ensures n == 0 ==> apow(g,elem,n) == g.identity
    {
        if n == 0 then g.identity else if n > 0 then g.compose(elem, apow(g, elem, n-1)) else if n < 0 then g.compose(g.inverse(elem), apow(g, elem, n+1)) else g.identity
    }

    lemma zandapowEqual<A(!new)>(g: Group, elem: A, z: int)
        requires ValidGroup(g)
        requires inGroup(g, elem)
        requires inGroup(g, g.identity)
        requires isIdentity(g)
        decreases z * z
        ensures apow(g, elem, z) == zpow(g, elem, z)
    {
        reveal isIdentity();
        if z >= 0 {
            assert apow(g, elem, z) == zpow(g, elem, z);
        }else{
            if z == -1 {
                GroupContainsInverse(g, elem);
                onePower(g, elem);
                assert g.identity == apow(g, elem, 0);
                assert elem == apow(g, elem, 1);
                calc{
                    apow(g, elem, -1);
                    g.compose(g.inverse(elem), apow(g, elem, -1+1));
                    g.compose(g.inverse(elem), g.identity);
                    g.inverse(elem);
                }
                assert g.inverse(elem) == apow(g, elem, -1);
                assert apow(g, elem, z) == zpow(g, elem, z);
            }else{
                zandapowEqual(g,elem, z+1);
                apowClosed(g, elem, z+1);
                GroupContainsInverse(g, elem);
                calc {
                    zpow(g, elem, z);
                    g.inverse(npow(g, elem, -z));
                }
                assert g.inverse(npow(g, elem, -(z+1))) == apow(g, elem, z+1);
                calc {
                    apow(g, elem, z);
                    g.compose(g.inverse(elem), apow(g, elem, z+1));
                    g.compose(g.inverse(elem), g.inverse(npow(g, elem, -(z+1))));
                    g.compose(g.inverse(elem), zpow(g, elem, (z+1)));
                    {zpowInverseComposeTwo(g, elem, z);}
                    zpow(g, elem,z);
                }
                assert apow(g, elem, z) == zpow(g, elem, z);
            }
        }
    }

    lemma apowPos<A>(g: Group, elem: A, n: int)
        requires n > 0
        ensures n > 0 ==> apow(g,elem,n) == g.compose(elem, apow(g, elem, n-1))
    {}

    lemma apowNegative<A>(g: Group, elem: A, n: int)
        requires !(n > 0)
        ensures n < 0 ==> apow(g,elem,n) == g.compose(g.inverse(elem), apow(g, elem, n+1))
    {}


    lemma onePower<A(!new)>(g: Group, elem: A)
        requires ValidGroup(g)
        requires elem in g.elements
        requires isIdentity(g)
        ensures apow(g, elem, 1) == elem
    {
        reveal isIdentity();
        calc {
            apow(g, elem, 1);
            g.compose(elem, apow(g, elem, 0));
            g.compose(elem, g.identity);
            elem;
        }
    }

    lemma oneMinusPower<A(!new)>(g: Group, elem: A)
        requires ValidGroup(g)
        // requires elem in g.elements
        requires inGroup(g, elem)
        // requires isIdentity(g)
        // requires closedInverse(g) && isInverse(g)
        ensures apow(g, elem, -1) == g.inverse(elem)
    {
        GroupContainsInverse(g, elem);
        calc {
            apow(g, elem, -1);
            g.compose(g.inverse(elem), apow(g, elem, 0));
            g.compose(g.inverse(elem), g.identity);
            == {GroupIdentity(g, g.inverse(elem));}
            g.inverse(elem);
        }
    }


    lemma {:verify true} apowClosed<A>(g: Group, elem: A, n: int)
        // requires elem in g.elements
        // requires g.identity in g.elements
        requires inGroup(g, elem)
        requires inGroup(g, g.identity)
        // requires isIdentity(g)
        // requires closedComposition(g)
        // requires closedInverse(g)
        // requires isInverse(g)
        // requires n >= 0
        decreases n*n
        ensures inGroup(g, apow(g, elem, n))
    {
        if n == 0 {
            assert apow(g, elem, 0) in g.elements;
        } else if n > 0 {
            apowPos(g, elem, n);
            apowClosed(g, elem, n-1);
            GroupClosedComposition(g, elem, apow(g, elem, n-1));
        }else {
            apowNegative(g,elem, n);
            apowClosed(g, elem, n+1);
            assert apow(g, elem, n+1) in g.elements;
            assert elem in g.elements;
            GroupContainsInverse(g, elem);
            GroupClosedComposition(g, g.inverse(elem), apow(g, elem, n+1));
            // calc {
            //     apow(g, elem, n);
            //     g.compose(g.inverse(elem), )
            // }
            assert apow(g, elem, n) in g.elements;
        }
}

    predicate inGroup<A>(g: Group, elem: A) {
        elem in g.elements
    }

    lemma {:verify true} allApowClosed<A>(g: Group, elem: A) 
        // requires closedComposition(g)
        // requires closedInverse(g)
        // requires g.identity in g.elements
        // requires elem in g.elements
        requires inGroup(g, g.identity)
        requires inGroup(g, elem)
        ensures forall x: int :: inGroup(g, apow(g, elem, x))
    {
        forall x: int | true 
        {
            apowClosed(g, elem, x);
        }
    }

    // method {:verify true} apowSubtract<A>(g: Group<A>, elem: A, n: int)
    lemma {:verify } {:induction false} apowSubtract<A(!new)>(g: Group<A>, elem: A, n: int)
        requires ValidGroup(g)
        // requires closedComposition(g)
        // requires closedInverse(g)
        // requires associativeComposition(g)
        // requires isIdentity(g)
        // requires isInverse(g)
        // requires g.identity in g.elements
        // requires elem in g.elements
        requires inGroup(g, g.identity)
        requires inGroup(g, elem)
        requires n >= 0
        // ensures g.compose(apow(g, elem, n), apow(g, elem, -1)) == apow(g, elem, n-1)
        ensures g.compose(apow(g, elem, -1), apow(g, elem, n)) == apow(g, elem, n-1)
    {
        allApowClosed(g, elem);
        assert inGroup(g, apow(g, elem, -1));
        assert inGroup(g, apow(g, elem, n));
        assert inGroup(g, apow(g, elem, n-1));
        assert inGroup(g, g.identity);
        if n > 0 {
            calc {
                g.compose(apow(g, elem, -1), apow(g, elem, n));
                == {apowPos(g,elem, n);}
                g.compose(apow(g, elem, -1), g.compose(elem, apow(g, elem, n-1)));
                == {GroupAssociativeComposition(g,apow(g, elem, -1), elem, apow(g, elem, n-1));}
                g.compose(g.compose(apow(g, elem, -1), elem), apow(g, elem, n-1));
                == {oneMinusPower(g, elem);}
                g.compose(g.compose(g.inverse(elem), elem), apow(g, elem, n-1));
                == {GroupInverse(g, elem);}
                g.compose(g.identity, apow(g, elem, n-1));
                == {GroupIdentity(g, apow(g, elem, n-1));}
                apow(g, elem, n-1);
            }
        }else if n == 0 {
            calc {
                g.compose(apow(g, elem, -1), apow(g, elem, 0));
                g.compose(apow(g, elem, -1), g.identity);
                == {GroupIdentity(g, apow(g, elem, -1));}
                apow(g, elem, -1);
            }
        }else{
            assert n < 0;
            assert (n-1)+1 == n;
            calc {
                g.compose(apow(g, elem, -1), apow(g, elem, n));
                == {oneMinusPower(g, elem);}
                g.compose(g.inverse(elem), apow(g, elem, n));
                apow(g, elem, n-1);
            }
        }
    }

    lemma apowAdditionAxiom<A>(g: Group<A>, elem: A, n: int, k: int)
        ensures g.compose(apow(g, elem, n), apow(g, elem, k)) == apow(g, elem, n+k)

    lemma apowAdditionAxiomNeg<A>(g: Group<A>, elem: A, n: int, k: int)
        ensures g.compose(apow(g, elem, -n), apow(g, elem, -k)) == apow(g, elem, -n-k)

    lemma {:verify true} apowAddition<A(!new)>(g: Group<A>, elem: A, n: nat, k: nat)
        // requires elem in g.elements
        // requires g.identity in g.elements
        requires inGroup(g, elem)
        requires inGroup(g, g.identity)
        requires ValidGroup(g)
        // requires closedComposition(g)
        // requires closedInverse(g)
        // requires inGroup(g, g.identity)
        // requires isIdentity(g)
        // requires associativeComposition(g)
        ensures g.compose(apow(g, elem, n), apow(g, elem, k)) == apow(g, elem, n+k)
    {
        allApowClosed(g, elem);
        if k == 0 {
            assert apow(g, elem, k) == g.identity;
            calc {
                apow(g, elem, n+k);
                apow(g, elem, n);
            }
            GroupIdentity(g, apow(g, elem, n));
            assert g.compose(apow(g, elem, n), g.identity) == apow(g, elem, n+k);
        }else if n == 0 {
            assert apow(g, elem, n) == g.identity;
            GroupIdentity(g, apow(g, elem, k));
            assert g.compose(g.identity, apow(g, elem, k)) == apow(g, elem, n+k);
        }else if n > 0 {
            apowPos(g,elem, n);
            calc {
                g.compose(apow(g, elem, n), apow(g, elem, k));
                g.compose(g.compose(elem, apow(g, elem, n-1)), apow(g, elem, k));
                == {GroupAssociativeComposition(g, elem, apow(g, elem, n-1), apow(g, elem, k));}
                g.compose(elem, g.compose(apow(g, elem, n-1), apow(g, elem, k)));
                == {apowAddition(g,elem, n-1,k);}
                g.compose(elem, apow(g, elem, n-1+k));
                apow(g, elem, n+k);
            }
        }
    }

    lemma npowInverse<A(!new)>(g: Group<A>, elem: A, n: int)
        requires n > 0
        requires elem in g.elements
        requires ValidGroup(g)
        ensures g.inverse(npow(g,elem, n)) == zpow(g, elem, -n)
    {

    }

    lemma zpowInverseCompose<A(!new)>(g: Group<A>, elem: A, z: int)
        requires z < 0
        requires elem in g.elements
        requires ValidGroup(g)
        decreases -z
        ensures g.compose(zpow(g, elem, (z+1)), g.inverse(elem)) == zpow(g, elem, z)
    {
        if z < -1 {
        assume npow(g,elem, -(z+1)) in g.elements;
        // zpowInverseCompose(g, elem, z+1);
        assert zpow(g, elem, z+1) == g.inverse(npow(g, elem, -(z+1)));
        calc{
            zpow(g, elem, z);
            g.inverse(npow(g,elem, -z));
            g.inverse(g.compose(elem, npow(g,elem, -(z+1))));
            {groupCompositionInverse(g, elem, npow(g,elem, -(z+1)), g.inverse(elem), g.inverse(npow(g,elem, -(z+1))), g.inverse(g.compose(elem, npow(g,elem, -(z+1)))));}
            g.compose(g.inverse(npow(g,elem, -(z+1))), g.inverse(elem));
            g.compose(zpow(g,elem, z+1), g.inverse(elem));
        }
        assert g.compose(zpow(g, elem, (z+1)), g.inverse(elem)) == zpow(g, elem, z);
        }else if z == -1 {
            assert npow(g, elem, 0) == g.identity;
            GroupInverse(g, elem);
            GroupContainsInverse(g, elem);
            GroupIdentity(g, elem);
            GroupIdentity(g, g.inverse(elem));
            calc{
                zpow(g, elem, z);
                g.inverse(npow(g,elem, -z));
                g.inverse(g.compose(elem, npow(g,elem, 0)));
                g.inverse(g.compose(elem, g.identity));
                g.inverse(elem);
            }
            calc {
                g.compose(zpow(g, elem, (z+1)), g.inverse(elem));
                g.compose(zpow(g, elem, 0), g.inverse(elem));
                g.compose(g.identity, g.inverse(elem));
                g.inverse(elem);
            }

        assert g.compose(zpow(g, elem, (z+1)), g.inverse(elem)) == zpow(g, elem, z);
        }
    }

    lemma zpowInverseComposeTwo<A(!new)>(g: Group<A>, elem: A, z: int)
        requires ValidGroup(g)
        requires z < 0
        requires elem in g.elements
        requires inGroup(g, elem)
        decreases -z
        ensures g.compose(g.inverse(elem), zpow(g, elem, (z+1))) == zpow(g, elem, z)
    {
        if z == -1 {
            assert npow(g, elem, 0) == g.identity;
            GroupInverse(g, elem);
            GroupContainsInverse(g, elem);
            GroupIdentity(g, elem);
            GroupIdentity(g, g.inverse(elem));
            calc{
                zpow(g, elem, z);
                g.inverse(npow(g,elem, -z));
                g.inverse(g.compose(elem, npow(g,elem, 0)));
                g.inverse(g.compose(elem, g.identity));
                g.inverse(elem);
            }
            calc {
                g.compose(g.inverse(elem), zpow(g, elem, (z+1)));
                g.compose(g.inverse(elem), zpow(g, elem, 0));
                g.compose(g.inverse(elem), g.identity);
                g.inverse(elem);
            }
            assert g.compose(g.inverse(elem), zpow(g, elem, (z+1))) == zpow(g, elem, z);
        }else{
            assume npow(g, elem, -(z+2)) in g.elements;
            assume npow(g, elem, -(z+1)) in g.elements;
            calc {
            zpow(g, elem, z);
            g.inverse(npow(g,elem, -z));
            g.inverse(g.compose(elem, npow(g,elem, -(z+1))));
            {npowPos(g, elem, -(z+1));}
            g.inverse(g.compose(elem, g.compose(npow(g, elem, -(z+2)), elem)));
            { GroupAssociativeComposition(g, elem, npow(g, elem, -(z+2)), elem);}
            g.inverse( g.compose( g.compose( elem, npow(g, elem, -(z+2)) ), elem));
            g.inverse( g.compose( npow(g, elem, -(z+1)), elem));
            {groupCompositionInverse(g, npow(g, elem, -(z+1)), elem, g.inverse(npow(g, elem, -(z+1))), g.inverse(elem), g.inverse( g.compose( npow(g, elem, -(z+1)), elem)));}
            g.compose(g.inverse(elem), g.inverse(npow(g, elem, -(z+1))));
            g.compose(g.inverse(elem), zpow(g, elem, z+1));
            }
        }
    }

    lemma apowInverse<A(!new)>(g: Group<A>, elem: A, n: int)
        requires ValidGroup(g)
        requires elem in g.elements
        // requires ValidGroup(g)
        ensures g.inverse(apow(g,elem, n)) == apow(g, elem, -n)
    // {
    //     if n == 0 {
    //         assert apow(g, elem, n) == g.identity;
    //         assert apow(g, elem, -n) == g.identity;
    //         assert g.inverse(g.identity) == g.identity;
    //     }else if n == 1 {
    //         apowNegative(g, elem, -1);
    //         // calc {
    //         //     apow(g, elem, -n);
    //         //     apow(g, elem, -1);
    //         //     g.compose(g.inverse(elem), apow(g, elem, 0));
    //         // }
    //         assert g.inverse(apow(g,elem, n)) == apow(g, elem, -n);
    //     }else{
    //         calc {
    //             g.inverse(apow(g, elem, n));
    //             g.inverse(g.compose(elem, apow(g, elem, n-1)));
    //         }
    //     }
    // }

    lemma {:verify false} apowAdditionInt<A(!new)>(g: Group<A>, elem: A, n: int, k: int)
        requires ValidGroup(g)
        requires elem in g.elements
        // requires ValidGroup(g)
        // requires closedComposition(g)
        // requires closedInverse(g)
        requires g.identity in g.elements
        // requires isIdentity(g)
        // requires associativeComposition(g)
        ensures g.compose(apow(g, elem, n), apow(g, elem, k)) == apow(g, elem, n+k)
    {
        // allApowClosed(g, elem);
        if k == 0 {
            assert apow(g, elem, k) == g.identity;
            // assert g.compose(apow(g, elem, n), g.identity) == apow(g, elem, n+k);
        }else if n == 0 {
            assert apow(g, elem, n) == g.identity;
            // assert g.compose(g.identity, apow(g, elem, k)) == apow(g, elem, n+k);
        }else if n > 0 && k > 0 {
            apowPos(g, elem, n);
            apowPos(g, elem, n+k);
            assert apow(g, elem, n-1) in g.elements;
            assert apow(g, elem, k) in g.elements;
            assert apow(g, elem, n+k) in g.elements;
            assume g.compose(elem, g.compose(apow(g, elem, n-1), apow(g, elem, k))) == g.compose(elem, apow(g, elem, n-1+k));
            calc {
                g.compose(apow(g, elem, n), apow(g, elem, k));
                g.compose(g.compose(elem, apow(g, elem, n-1)), apow(g, elem, k));
                g.compose(elem, g.compose(apow(g, elem, n-1), apow(g, elem, k)));
                // == {apowAdditionInt(g,elem, n-1,k);}
                g.compose(elem, apow(g, elem, n-1+k));
                apow(g, elem, n+k);
            }
        // }else{

        }else if n > 0  && k < 0 {
            var q := n+k;
            if n+k >= 0 {

            }else if n+k < 0 {
                var z :| 0 - z == q;
                assert k == -n-z;
                assert z > 0;
                calc {
                    g.compose(apow(g, elem, n), apow(g, elem, k));
                    g.compose(apow(g, elem, n), apow(g, elem, -n-z));
                    == {apowAdditionAxiomNeg(g, elem, n, z);}
                    g.compose(apow(g, elem, n), g.compose(apow(g, elem, -n), apow(g, elem, -z)));
                    g.compose(g.compose(apow(g, elem, n), apow(g, elem, -n)), apow(g, elem, -z));
                    == {apowAdditionAxiom(g, elem, n,-n);}
                    g.compose(apow(g, elem, n-n), apow(g, elem, -z));
                    g.compose(apow(g, elem, 0), apow(g, elem, -z));
                    g.compose(g.identity, apow(g, elem, -z));
                    apow(g, elem, -z);
                }
            }
        }else if n < 0 && k > 0 {
            var q := n+k;

        }else if n < 0 && k < 0 {

        }
    }

    lemma positiveNumbersArePositive(k: nat, s: nat)
        requires k >= 0
        requires s >= 0
        ensures Math.prod(k , s) >= 0
    {
        reveal Math.prod();
    }

    lemma positiveNumbersAreStilPositive(k: nat, s: nat, x: nat, y: nat)
        requires k >= 0
        requires s >= 0
        requires x >= 0
        requires y >= 0
        ensures Math.prod(k , s) + Math.prod(x,y) >= 0
    {
        positiveNumbersArePositive(k,s);
        positiveNumbersArePositive(x,y);
        // reveal Math.prod();
    }

    lemma apowSub<A>(g: Group, elem: A, x: int, y: int)
        requires x - y == sub(x,y)
        ensures apow(g, elem, x-y) == apow(g, elem, sub(x,y))
    {

    }

    lemma apowAdd<A>(g: Group, elem: A, k: int, x: int, y: int)
        ensures apow(g, elem, k+Math.prod(x,y)) == apow(g, elem, Math.prod(k,1) + Math.prod(x,y))
    {
        Math.prodIdentity(k);
    }

    lemma apowReduce<A>(g: Group, elem: A, k: nat, s: nat) 
        requires s >= 1
        ensures apow(g, elem, k+Math.prod(k,sub(s,1))) == apow(g, elem, Math.prod(k,s))
    {
        Math.prodIdentity(k);
        assert k + Math.prod(k, sub(s,1)) == Math.prod(k,1) + Math.prod(k, sub(s,1));
        calc {
            apow(g, elem, k+Math.prod(k,sub(s,1)));
            apow(g, elem, Math.prod(k,1) + Math.prod(k, sub(s,1)));
            == {prodDistributesSub(k, 1, s);}
            apow(g, elem, Math.prod(k, s));
        }

    }

    lemma {:verify }  something<A(!new)>(g: Group<A>, elem: A, k: nat, s: nat)
        requires elem in g.elements
        requires ValidGroup(g)
        // requires closedComposition(g)
        // requires closedInverse(g)
        requires g.identity in g.elements
        // requires isIdentity(g)
        // requires associativeComposition(g)
        requires s >= 1
        // ensures g.compose(apow(g, elem, k), apow(g, elem, k*(s-1))) == apow(g, elem, k + k*(s-1))
         ensures g.compose(apow(g, elem, k), apow(g, elem, Math.prod(k,(s-1)))) == apow(g, elem, k+Math.prod(k,(s-1)))
    {
        reveal Math.prod();
        assert Math.prod(k, (s-1)) >= 0;
        apowAddition(g, elem, k, Math.prod(k,(s-1)));
    }

    lemma something2<A>(g: Group<A>, elem: A, k: nat, s: nat)
        requires s >= 1
        ensures apow(g, elem, k*s) == apow(g, elem, k + k*(s-1))
    {
        // assert k+k*(s-1) == k * s;
    }

    lemma {:verify false}  apowExponentNat<A(!new)>(g: Group<A>, elem: A, k: nat, s: nat)
        requires elem in g.elements
        requires ValidGroup(g)
        requires closedComposition(g)
        requires closedInverse(g)
        requires g.identity in g.elements
        requires isIdentity(g)
        requires associativeComposition(g)
        ensures apow(g, apow(g, elem, k), s) == apow(g, elem, k*s)
    {
        if s == 0 {
            // assert k * s == 0;
            // assert s == 0;
            // assert apow(g,apow(g,elem,k),s) == g.identity;
        }else if s > 0 {
            // assume apow(g, apow(g, elem, k), s-1) == apow(g, elem, k*(s-1));
            calc {
                apow(g, apow(g, elem, k), s);
                g.compose(apow(g, elem, k), apow(g, apow(g, elem, k), s-1));
                == {apowExponentNat(g, elem, k, (s-1));}
                g.compose(apow(g, elem, k), apow(g, elem, k*(s-1)));
                == {something(g,elem, k, s);}
                // == {apowAddition(g, elem, k, k*(s-1));}
                apow(g, elem, k+k*(s-1));
                == {something2(g, elem,k,s);} //will verify without this but will do it slower
                apow(g, elem, k*s);
            }
        }
    }

    lemma {:verify }  apowExponentInt<A>(g: Group<A>, elem: A, k: int, s: int)
        requires inGroup(g, elem)
        requires inGroup(g, g.identity)
        ensures apow(g, apow(g, elem, k), s) == apow(g, elem, Math.prod(k,s))

    lemma {:verify }  apowExponent<A(!new)>(g: Group<A>, elem: A, k: nat, s: nat)
        requires inGroup(g, elem)
        requires inGroup(g, g.identity)
        requires ValidGroup(g)
        // requires closedComposition(g)
        // requires closedInverse(g)
        // requires inGroup(g, g.identity)
        // requires isIdentity(g)
        // requires associativeComposition(g)
        // ensures apow(g, apow(g, elem, k), s) == apow(g, elem, k*s);
        ensures apow(g, apow(g, elem, k), s) == apow(g, elem, Math.prod(k,s))
    {
        allApowClosed(g,elem);
        allApowClosed(g,apow(g,elem, k));
        if s == 0 {
            assert k * s == 0;
            assert s == 0;
            assert apow(g,apow(g,elem,k),s) == g.identity;
            prodZero(k,s);
            assert Math.prod(k,s) == 0;
        }else if s > 0 {
            positiveNumbersArePositive(k, s);
            positiveNumbersArePositive(k, sub(s,1));
            positiveNumbersAreStilPositive(k,1,k,sub(s,1));
            assert Math.prod(k,1)+Math.prod(k,sub(s,1)) >= 0;
            // // assume apow(g, apow(g, elem, k), sub(s,1)) == apow(g, elem, Math.prod(k,sub(s,1)));
            assert k + Math.prod(k,sub(s,1)) >=0;
            calc {
                apow(g, apow(g, elem, k), s);
                g.compose(apow(g, elem, k), apow(g, apow(g, elem, k), s-1));
                == {apowSub(g, apow(g, elem, k), s, 1);}
                g.compose(apow(g, elem, k), apow(g, apow(g, elem, k), sub(s,1)));
                == {apowExponent(g, elem, k, sub(s,1));}
                g.compose(apow(g, elem, k), apow(g, elem, Math.prod(k,sub(s,1))));
                == {apowAddition(g,elem, k, Math.prod(k,sub(s,1)));}
                apow(g, elem, k+Math.prod(k,sub(s,1)));
                 == {apowReduce(g, elem, k, s);}
                apow(g, elem, Math.prod(k,s));
            }
        }
    }

    lemma {:verify }  apowExponentIn<A(!new)>(g: Group<A>, elem: A, k: nat, s: nat)
        requires ValidGroup(g)
        requires inGroup(g, elem)
        requires inGroup(g, g.identity)
        ensures inGroup(g, apow(g, elem, Math.prod(k,s)))
    {
        apowClosed(g, elem, Math.prod(k, s));
    }

    ghost predicate CyclicGroupGeneratedBy<A(!new)>(g: Group, elem: A)
        requires elem in g.elements
    {
        exists n :: n == |g.elements| &&
            n > 0 &&
            apow(g, elem, n) == g.identity &&
            (forall i :: 1 < i < n ==> apow(g, elem, i) != g.identity)  &&
            forall x :: x in g.elements ==> exists i :: 0 <= i < n && apow(g, elem, i) == x
    }

    ghost predicate isIsomorphism<A(!new),B(!new)>(g: Group<A>, g': Group<B>, phi: A -> B)
        requires ValidGroup(g)
        requires ValidGroup(g')
    {
        phi(g.identity) == g'.identity &&
        forall x :: x in g.elements ==> (phi(x) in g'.elements &&
        forall x,y :: x in g.elements && y in g.elements ==> phi(g.compose(x,y)) == g'.compose(phi(x), phi(y)))
    }

    lemma Artin2_3_b<A(!new),B(!new)>(g: Group<A>, g': Group<B>, phi: A -> B, x: A, y: A) 
        requires ValidGroup(g)
        requires ValidGroup(g')
        requires isIsomorphism(g, g', phi)
        requires x in g.elements && y in g.elements
        requires g.compose(x, g.compose(y,x)) == g.compose(y, g.compose(x, y))
        ensures g'.compose(phi(x), g'.compose(phi(y), phi(x))) == g'.compose(phi(y), g'.compose(phi(x), phi(y)))
    {
        reveal ValidGroup();
        reveal isIdentity();
        reveal closedComposition();
    }

    lemma Artin2_3_c<A(!new),B(!new)>(g: Group<A>, g': Group<B>, phi: A -> B, x: A) 
        requires ValidGroup(g)
        requires ValidGroup(g')
        requires isIsomorphism(g, g', phi)
        requires x in g.elements
        ensures g'.inverse(phi(x)) == phi(g.inverse(x))
    {

        reveal ValidGroup();
        reveal isIdentity();
        assert g.compose(x, g.inverse(x)) == g.identity;
        assert g'.compose(phi(x), phi(g.inverse(x))) == phi(g.identity) == g'.identity;
        assert g.compose(g.inverse(x), x) == g.identity;
        assert g'.compose(phi(g.inverse(x)), phi(x)) == phi(g.identity) == g'.identity;
        areInverses(g',phi(g.inverse(x)), phi(x));
    }

    lemma subsetsSmaller<T>(a: set<T>, b: set<T>)
        requires a <= b
        ensures |a| <= |b|
    // {
    //     if x :| x in a {
    //         assert x in b;
    //         subsetsSmaller(a-{x}, b);
    //         assert |a|== 1 + |a-{x}|; 
    //         if |a| == |b| {
                
    //         }else{
    //             assert |a| < |b|;
    //         }
    //     }
        
    // }
    lemma {:verify } AllSubgroupsOfCyclicSubgroupsAreCyclicGenerated<A(!new)>(g: Group, elem: A, h:Group, n: int)
        requires n >= 0
        requires elem in g.elements
        requires elem in h.elements
        requires CyclicGroupGeneratedBy(g, elem)
        requires ValidGroup(g)
        requires h.elements <= g.elements
        requires ValidGroup(h)
        requires ValidSubGroup(g, h)
        ensures apow(h, elem, n) == apow(g, elem, n)
        ensures apow(h, elem, n) in h.elements
    {
        if n == 0 {
            // assert apow(h, elem, 0) == h.identity;
        } else if n == 1 {
            // VGAIdentity(g);
            reveal ValidGroup();
            onePower(h, elem);
            // assert apow(h, elem, 1) == elem;
        } else{
            GroupClosedComposition(h, elem, apow(h, elem, n-1));

        }
    }

    lemma {:verify } AllSubgroupsOfCyclicSubgroupsAreCyclicGenerated2<A(!new)>(g: Group, elem: A, h:Group, n: int, t: A, i: int)
        requires elem in g.elements
        requires t in g.elements && t in h.elements
        requires t == apow(g, elem, i)
        requires CyclicGroupGeneratedBy(g, elem)
        requires ValidGroup(g)
        requires h.elements <= g.elements
        requires ValidGroup(h)
        requires ValidSubGroup(g, h)
        decreases n*n
        // ensures apow(h, elem, n) == apow(g, elem, n)
        ensures apow(h, t, n) in h.elements && apow(h, t, n) in g.elements
        ensures apow(h, t, n) == apow(g, elem, Math.prod(i, n))
    {
        if (n >=0) {
        if n == 0 {
            assert apow(h, t, 0) == h.identity;

            calc {
                Math.prod(i,n);
                {reveal Math.prod();}
                0;
            }
        } else if n == 1 {
            VGAIdentity(g);
            VGAIdentity(h);
            reveal isIdentity();
            assert apow(h, t, 1) == t;
            calc {
                Math.prod(i,n);
                {reveal Math.prod();}
                i;
            }
            assert apow(h, t, n) == apow(g, elem, Math.prod(i, n));
        } else{
            AllSubgroupsOfCyclicSubgroupsAreCyclicGenerated2(g, elem, h, n-1, t, i);
            GroupClosedComposition(h, t, apow(h, t, n-1));
            apowExponentInt(g, elem, i, n-1);
            assert apow(h, t, n-1) == apow(g, elem, Math.prod(i, n-1));
            // assert apow(h, t, n) == h.compose(t, apow(h, t, n-1));
            assert i + Math.prod(i, n-1) == Math.prod(i, n) by {
                reveal Math.prod();
            }
            calc{
                apow(h, t, n);
                h.compose(t, apow(h, t, n-1));
                g.compose(t, apow(h, t, n-1));
                g.compose(t, apow(g, elem, Math.prod(i, n-1)));
                g.compose(apow(g, elem, i), apow(g, elem, Math.prod(i, n-1)));
                {apowAdditionInt(g,elem, i, Math.prod(i, n-1));}
                apow(g, elem, Math.prod(i, n));
            }

            assert apow(h, t, n) == apow(g, elem, Math.prod(i, n));

        }
        }else{
            AllSubgroupsOfCyclicSubgroupsAreCyclicGenerated2(g, elem, h, n+1, t, i);

            GroupContainsInverse(h, t);
            GroupInverse(h, t);
            GroupClosedComposition(h, h.inverse(t), apow(h, t, n+1));
            assert -i + Math.prod(i, n+1) == Math.prod(i, n) by {
                reveal Math.prod();
            }
            calc{
                apow(h, t, n);
                h.compose(h.inverse(t), apow(h, t, n+1));
                g.compose(h.inverse(t), apow(h, t, n+1));
                g.compose(h.inverse(t), apow(g, elem, Math.prod(i, n+1)));
                g.compose(g.inverse(apow(g, elem, i)), apow(g, elem, Math.prod(i, n+1)));
                {apowInverse(g, elem,i);}
                g.compose(apow(g, elem, -i), apow(g, elem, Math.prod(i, n+1)));
                {apowAdditionInt(g, elem, -i, Math.prod(i, n+1));}
                apow(g, elem, Math.prod(i, n));
            }
            assert apow(h, t, n) == apow(g, elem, Math.prod(i, n));
        }
    }

    lemma {:verify } AllSubgroupsOfCyclicSubgroupsAreCyclicGeneratedSame<A(!new)>(g: Group, elem: A, h:Group)
        requires elem in g.elements
        requires elem in h.elements
        requires CyclicGroupGeneratedBy(g, elem)
        requires ValidGroup(g)
        requires h.elements <= g.elements
        requires ValidGroup(h)
        requires ValidSubGroup(g, h)
        ensures h.elements == g.elements
    {
        var n :| n == |g.elements| &&
            n > 0 &&
            apow(g, elem, n) == g.identity &&
            (forall i :: 1 < i < n ==> apow(g, elem, i) != g.identity)  &&
            forall x :: x in g.elements ==> exists i :: 0 <= i < n && apow(g, elem, i) == x;
        forall x | x in g.elements
            ensures x in h.elements
        {
           var i :| 0 <= i < n && apow(g, elem, i) == x;
           AllSubgroupsOfCyclicSubgroupsAreCyclicGenerated(g, elem, h, i);
        }
    }
    
    lemma {:verify } AllSubgroupsOfCyclicSubgroupsAreCyclicIfDifferent<A(!new)>(g: Group, elem: A, h:Group, y: A, z: A)
        requires elem in g.elements
        requires elem != g.identity
        requires y != z
        requires y != g.identity && z != g.identity
        requires y != elem && z != elem
        requires z in h.elements
        requires y in h.elements
        requires CyclicGroupGeneratedBy(g, elem)
        requires ValidGroup(g)
        requires h.elements <= g.elements
        requires ValidGroup(h)
        requires ValidSubGroup(g, h)
        ensures exists hx: A :: hx in h.elements && CyclicGroupGeneratedBy(h, hx)
    {
        var n :| n == |g.elements| &&
            n > 0 &&
            apow(g, elem, n) == g.identity &&
            (forall i :: 1 < i < n ==> apow(g, elem, i) != g.identity)  &&
            forall x :: x in g.elements ==> exists i :: 0 <= i < n && apow(g, elem, i) == x;
        assert isIdentity(g) by {
            reveal ValidGroup();
        }
        reveal isIdentity();
        // var common := Math.Gcd(i, k);
        if elemA: A, elemB: A, i: int, k: int :| elemA != elemB && inGroup(h, elemA) && inGroup(h, elemB) && 1 <= i < n && apow(g, elem, i) == elemA && 1 <= k < n && apow(g, elem, k) == elemB && Math.Gcd(i,k) == 1 {
            VGAIdentity(g);
            reveal isIdentity();
            onePower(g, elem);
            allApowClosed(g, elem);
            // allApowClosed(h, elem);
            Math.GcdLinearCombination(i, k);
            var u,v :| Math.Gcd(i,k) == Math.linearCombination(i,u,k,v);
            assert Math.prod(i, u) + Math.prod(k, v) == 1; 
            // assert y in g.elements;
            apowExponentInt(g,elem,i, u);
            assert apow(g, apow(g, elem, i), u) == apow(g, elem, Math.prod(i, u));
            AllSubgroupsOfCyclicSubgroupsAreCyclicGenerated2(g, elem, h, u, apow(g, elem, i), i);
            assert apow(h, elemA, u) == apow(g, elem, Math.prod(i, u));

            AllSubgroupsOfCyclicSubgroupsAreCyclicGenerated2(g, elem, h, v, apow(g, elem, k), k);
            apowExponentInt(g,elem,k, v);
            assert apow(h, elemB, v) == apow(g, elem, Math.prod(k, v));
            // assert apow(g, apow(g, elem, i), x) == apow(g, elem, Math.prod(i,x));

            calc {
                g.compose(apow(g, elem, Math.prod(i, u)), apow(g, elem, Math.prod(k, v)));
                {apowAdditionInt(g, elem, Math.prod(i, u) , Math.prod(k, v));}
                apow(g, elem, Math.prod(i, u) + Math.prod(k, v));
                // apow(h, elem, Math.prod(i, x) + Math.prod(k, y));
                apow(h, elem, 1);
                elem;
            }

            GroupClosedComposition(h, apow(g, elem, Math.prod(i, u)), apow(g, elem, Math.prod(k, v)));
            assert elem in h.elements;
            AllSubgroupsOfCyclicSubgroupsAreCyclicIfElem(g, elem, h);
        }else{
            assert !(exists elemA: A, elemB: A, i: int, k: int :: elemA != elemB && inGroup(h, elemA) && inGroup(h, elemB) && 1 <= i < n && apow(g, elem, i) == elemA && 1 <= k < n && apow(g, elem, k) == elemB && Math.Gcd(i,k) == 1);
            assert y in g.elements;
            assert z in g.elements;
            var i :| 0 <= i < n && apow(g, elem, i) == y;
            var k :| 0 <= k < n && apow(g, elem, k) == z;
            onePower(g, g.identity);
            assert i > 1;
            assert k > 1;
            assert forall elemA: A, elemB: A, i: int, k: int :: elemA != elemB && inGroup(h, elemA) && inGroup(h, elemB) && 1 <= i < n && apow(g, elem, i) == elemA && 1 <= k < n && apow(g, elem, k) == elemB ==> Math.Gcd(i,k) != 1;

        }
    }

    lemma {:verify } AllSubgroupsOfCyclicSubgroupsAreCyclicIfElem<A(!new)>(g: Group, elem: A, h:Group)
        requires elem in g.elements
        requires elem != g.identity
        requires elem in h.elements
        requires CyclicGroupGeneratedBy(g, elem)
        requires ValidGroup(g)
        requires h.elements <= g.elements
        requires ValidGroup(h)
        requires ValidSubGroup(g, h)
        ensures exists hx: A :: hx in h.elements && CyclicGroupGeneratedBy(h, hx)
    {

        var n :| n == |g.elements| &&
            n > 0 &&
            apow(g, elem, n) == g.identity &&
            (forall i :: 1 < i < n ==> apow(g, elem, i) != g.identity)  &&
            forall x :: x in g.elements ==> exists i :: 0 <= i < n && apow(g, elem, i) == x;
        var y :| y in h.elements && y == elem;
        AllSubgroupsOfCyclicSubgroupsAreCyclicGeneratedSame(g, elem, h);
        assert h.elements == g.elements;
        assert |h.elements| == |g.elements|;
        assert forall i :: 0 <= i <= n ==> apow(h, elem, i) == apow(g, elem, i) by {
            forall i | 0 <= i <= n
                ensures apow(h, elem, i) == apow(g, elem, i)
            {
                AllSubgroupsOfCyclicSubgroupsAreCyclicGenerated(g, elem, h, i);
            }
        }
        assert y in h.elements && CyclicGroupGeneratedBy(h, y);
    }

    lemma {:verify } AllSubgroupsOfCyclicSubgroupsAreCyclic<A(!new)>(g: Group, elem: A, h:Group)
        requires elem in g.elements
        requires elem != g.identity
        requires CyclicGroupGeneratedBy(g, elem)
        // requires ValidGroupAxiom(g)
        requires ValidGroup(g)
        requires h.elements <= g.elements
        // requires ValidGroupAxiom(h)
        requires ValidGroup(h)
        requires ValidSubGroup(g, h)
        ensures exists hx: A :: hx in h.elements && CyclicGroupGeneratedBy(h, hx)
    {
        var n :| n == |g.elements| &&
            n > 0 &&
            apow(g, elem, n) == g.identity &&
            (forall i :: 1 < i < n ==> apow(g, elem, i) != g.identity)  &&
            forall x :: x in g.elements ==> exists i :: 0 <= i < n && apow(g, elem, i) == x;
        assert |h.elements| > 0;
        // var d :| d > 0 && Math.prod(d, |h.elements|) == n;
        if elem in h.elements {
            AllSubgroupsOfCyclicSubgroupsAreCyclicIfElem(g, elem, h);
        }else{
            var y :| y in h.elements && y != elem;
            if z :| z in h.elements && z != y {
                VGAIdentity(g);
                reveal isIdentity();
                onePower(g, g.identity);
                assert z in g.elements;
                var i :| 0 <= i < n && apow(g, elem, i) == y;
                assert i != 1;
                var k :| 0 <= k < n && apow(g, elem, k) == z;
                assert k != i;
                if k ==1 {
                    assert apow(g, elem, k) == elem;
                    assert z in h.elements;
                    assert elem in h.elements;
                    AllSubgroupsOfCyclicSubgroupsAreCyclicIfElem(g, elem, h);
                }else if k != 0 && i != 0 {
                    assert z != g.identity;
                    AllSubgroupsOfCyclicSubgroupsAreCyclicIfDifferent(g, elem, h, y, z);
                }else{
                   if k == 0 {
                    if w :| w in h.elements && w != z && w != y {
                    AllSubgroupsOfCyclicSubgroupsAreCyclicIfDifferent(g, elem, h, y, w);

                    }else{
                        assert h.elements == {h.identity, y};
                        assert apow(h, y, 2) == h.identity by {
                            GroupContainsInverse(h, y);
                            GroupInverse(h, y);
                        }
                        assert CyclicGroupGeneratedBy(h, y);
                    }
                   }else if i == 0 {
                    if w :| w in h.elements && w != z && w != y {
                    AllSubgroupsOfCyclicSubgroupsAreCyclicIfDifferent(g, elem, h, z, w);

                    }else{
                        assert h.elements == {h.identity, z};
                        assert apow(h, z, 2) == h.identity  by {
                            GroupContainsInverse(h, z);
                            GroupInverse(h, z);
                        }
                        assert CyclicGroupGeneratedBy(h, z);
                    }
                   } 
                }
            }else{
                VGAIdentity(h);
                onePower(h, h.identity);
                assert y == h.identity;
                assert h.elements == {h.identity};
                assert CyclicGroupGeneratedBy(h, h.identity);
            }
        }
        


    }

    export reveals *
}