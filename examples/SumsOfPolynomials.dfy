//https://whileydave.com/2023/07/17/proving-a-beautiful-identity-in-dafny/
module PolynomialSums {
    
function Sum(n:nat) : nat 
    requires n > 0
{
  if n == 1 then 1
  else 
    Sum(n-1) + n
}

function Sum3(n:nat) : nat 
    requires n > 0
{
  if n == 1 then 1 
  else 
     Sum3(n-1) + (n*n*n)
}

lemma Identity(n:nat) 
    requires n > 0 
    ensures Sum(n) * Sum(n) == Sum3(n) 
{
  if n != 1 {
    var m := n-1;
    Identity(m);
    // assert Sum(n)*Sum(n) == Sum(m)*Sum(m) + n*n*n;	
    assert Sum3(n) == Sum(m)*Sum(m) + n*n*n;
    } 
}

lemma Sum1toN(n:nat) 
    requires n > 0 
    ensures n * (n + 1) / 2 == Sum(n)
{}

lemma NNm1Mod2(n:nat) 
    requires n > 0
    ensures (n*(n-1)) % 2 == 0
{
  if n%2 == 0 { Mod2(n,n-1); } 
  else {
    Mod2(n-1,n);
    assert ((n-1)*n) % 2 == 0;
  }
}

lemma Mod2(n:nat,m:nat) 
    requires n%2 == 0
    ensures (n*m) % 2 == 0
{
  if m > 0 {
    Mod2(n,m-1);
    calc{
        n*m;
        n*(m-1) + n;
    }
  }
}

}