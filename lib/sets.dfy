
module SetCustom {
    export reveals *

    ghost function Union<T>(s: set<set<T>>): set<T> 
    {
        if s == {} then 
            assert forall x :: x in s ==> x <= {};
            {} 
        else
            var x :| x in s;
            x + Union(s - {x})
    }


    lemma UnionPlusSuperset<T>(s: set<set<T>>, x: set<T>, y: set<T>)
        requires x <= y
        requires x in s
        requires forall y :: y in s ==> y != {}
        ensures Union(s)+y == Union(s-{x} + {y})
        decreases s
    {
        if s == {} {

        }else{
            UnionPlusOne(s-{x}, x);
            calc{
                Union(s-{x}+{x});
                Union(s-{x}) + x;
                {assert s-{x}+{x} == s;} 
                Union(s);
            }
            UnionPlusOneIdempotent(s-{x}, y);

        }
    }

    lemma UnionPlusOneIdempotent<T>(s: set<set<T>>, x: set<T>)
        requires x != {}
        requires forall y :: y in s ==> y != {}
        ensures Union(s + {x}) == Union(s) + x
        decreases s
    {
        if s == {} {
        } else if x !in s {
            UnionPlusOne(s, x);
        }else{
            assert s+{x} == s;
            assert Union(s+{x}) == Union(s);
            UnionHasAll(s);
        }
    }
    lemma UnionPlusOne<T>(s: set<set<T>>, x: set<T>)
        requires x != {}
        requires forall y :: y in s ==> y != {}
        requires x !in s
        ensures Union(s + {x}) == Union(s) + x
        decreases s
    {
        if s == {} {
        } else {
            assert s+{x} != {};
            var z :| z in s + {x} && Union(s+{x}) == z + Union((s+{x})- {z} );
            if z == x {

            }else {
                UnionPlusOne(s-{z}, x);
                assert s -{z} + {x} == s+{x}-{z};
                UnionPlusOne(s-{z}, z);
                assert s -{z} + {z} == s ;
                calc {
                    Union(s+{x});
                    z + Union(s+ {x}-{z});
                    Union(s+ {x}-{z})+z;
                    Union(s-{z})+x+z;
                    Union(s-{z})+z+x;
                }
            }
        }
    }

    lemma UnionContains<T>(s: set<set<T>>, x: T)
        requires x in Union(s)
        ensures exists y :: y in s && x in y
    {
    }
    
    lemma UnionHasAll<T>(s: set<set<T>>)
        ensures forall x :: x in s ==> x <= Union(s)
        ensures forall y :: y in s ==> forall x :: x in y ==> x in Union(s)
    {
        if s == {} {
        } else {
            var x :| x in s && Union(s) == x + Union(s - {x});
            UnionHasAll(s - {x});
            forall y | y in s
                ensures y <= x + Union(s-{x}) 
            {
                if y == x {
                    assert y <= x;
                } else {
                    assert y in s-{x};
                }
            }
        }
    }

}