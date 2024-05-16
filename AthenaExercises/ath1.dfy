
module M {

abstract module Group {
  type T(==)
  const elems : set<T>
  const I : T
  
  function compose(a: T, b: T): (r: T)
    requires a in elems && b in elems
    ensures r in elems

  function inverse(a: T) : (r: T)
    requires a in elems
    ensures r in elems

  lemma LeftIdentity(x: T)
    requires x in elems
    requires I in elems
    ensures compose(I, x) == x

  lemma RightIdentity(x: T)
    requires x in elems
    requires I in elems
    ensures compose(x, I) == x

  lemma RightInverse(x: T)
    requires x in elems
    requires I in elems
    ensures compose(x, inverse(x)) == I

  lemma Associativity(a: T, b: T, c: T)
    requires a in elems && b in elems && c in elems
    ensures compose(a, compose(b, c)) == compose(compose(a, b), c)

  lemma InverseInverse(x: T)
    requires x in elems
    requires I in elems
    ensures inverse(inverse(x)) == x
  {
    calc {
        inverse(inverse(x));
        {LeftIdentity(inverse(inverse(x)));}
        compose(I, inverse(inverse(x)));
        {RightInverse(x);}
        compose(compose(x, inverse(x)), inverse(inverse(x)));
        {Associativity(x, inverse(x), inverse(inverse(x)));}
        compose(x, compose(inverse(x), inverse(inverse(x))));
        {RightInverse(inverse(x));}
        compose(x, I);
        {RightIdentity(x);}
        x;
    }
  }
  }
}