include "../definitions.dfy"
module CummingsCh1 {
    import opened Analysis

lemma exercise1_5<T>(A: set<T>, B: set<T>)
    requires A + B == A
    ensures B <= A
{

}


lemma exercise1_6<T,U>(f: T  -> U, f_inv: U -> T, B: set<U>)
    requires forall u: U :: f(f_inv(u)) == u
    ensures Range(f, Range(f_inv, B)) <= B
{

}

lemma exercise1_6c<T,U>(f: T  -> U, f_inv: U -> T, A: set<T>)
    // requires forall u: U :: f(f_inv(u)) == u
    requires forall a: T :: a in A ==> f_inv(f(a)) == a
    ensures A <= Range(f_inv, Range(f, A))
{

}

lemma exercise1_7<X(!new), Y(!new)>(f: X -> Y, g: Y -> X)
    requires forall x: X :: g(f(x)) == x
    ensures Injective(f) && Surjective(g)
{
    if !Injective(f) {
        var x,y: X :| x != y && f(x) == f(y);
        assert g(f(x)) == g(f(y));
        assert false;
    } else if !Surjective(g) {
        // assert exists b: Y :: !(exists a: X :: f(a) == b);
        // assert !(forall b: X :: exists a: Y :: g(a) == b);
        // var b: X :| !(exists a: Y :: g(a) == b);
        var b: X :| forall a: Y :: g(a) != b;
        assert g(f(b)) != b;
        assert false;
    }
}

lemma exercise1_23(A: iset<real>, B: iset<real>, abound: real, bbound: real, epsilon: real)
    requires A <= B
    requires sup(A, abound)
    requires sup(B, bbound)
    requires epsilon > 0.0
    ensures abound <= bbound
{
  if abound > bbound {
    var myepsilon := abound - bbound;
    assert bbound == sub(abound, myepsilon);
    assert upperBound(A, bbound);
    assert upperBound(A, sub(abound, myepsilon));
    assert  false;
  }
}

lemma example1_25(A: iset<real>)
    requires A == iset x: real | x < 0.0
    ensures sup(A, 0.0)
{
    assert forall x: real :: x in A ==> x < 0.0;
    assert upperBound(A, 0.0);
    forall epsilon: real | epsilon > 0.0
        ensures !upperBound(A, sub(0.0,epsilon))
    {
        calc ==> {
            epsilon > 0.0;
            - epsilon > -2.0 * epsilon;
            (- epsilon)/2.0 > -epsilon;
        }
        assert (-epsilon)/2.0 in A;
        assert (-epsilon)/2.0 > sub(0.0,epsilon);
        // assert !upperBound(A, )
    }
    assert leastUpperBound(A, 0.0);
}

function e29(n: nat): real {
    (n as real)/(n as real + 1.0)
}

lemma exercise1_29a(A: iset<real>)
    requires A == iset n: pos :: e29(n)
    ensures sup(A, 1.0)
{
    assert upperBound(A, 1.0);
    forall epsilon: real | epsilon > 0.0 
        ensures !upperBound(A, sub(1.0, epsilon))
    {
        ArchimedeanPrinciple(epsilon);
        var n: pos :| 1.0 / (n as real) < epsilon; 
        assert (1.0 / (n as real + 1.0)) < 1.0 / (n as real);
        assert e29(n) in A;
        assert sub(1.0, 1.0 / (n as real + 1.0)) == e29(n); 
        // assert exists k :: k in A && k > sub(1.0, epsilon);
    }
}

lemma exercise1_29b(A: iset<real>)
    requires A == iset n: pos :: e29(n)
    ensures inf(A, 1.0/2.0)
{
    assert e29(1) in A;
    forall x | x in A 
        ensures x >= 1.0/2.0
    {
        var n: nat :| x == e29(n);
        if n == 1 {
            assert x == 1.0/2.0;
        }else{
            assert (n as real)/(n as real + 1.0) >= 1.0/2.0;
        }
    }
    assert lowerBound(A, 1.0/2.0);
    assert greatestLeastBound(A, 1.0/2.0);
}

lemma exercise1_30(A: iset<real>, B: iset<real>, abound: real, bbound: real)
    requires sup(A, abound)
    requires sup(B, bbound)
    requires abound < bbound
    ensures exists b: real :: b in B && upperBound(A, b)
{
    // assert upperBound(A, bbound);
    // assert leastUpperBound(B, bbound);
    // assert forall epsilon: real :: epsilon > 0.0 ==> !upperBound(B, sub(bbound, epsilon));
    var epsilon := sub(bbound, abound);
    // assert abound + epsilon == bbound;
    // assert epsilon > 0.0;
    assert !upperBound(B, sub(bbound, epsilon));
}
}