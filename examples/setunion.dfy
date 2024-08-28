
module SOSetUnion {
predicate AllIn<T>(S: set<set<T>>, SU: set<T>) {
  forall xx :: xx in S ==> forall y :: y in xx ==> y in SU
}

predicate AllSingletonSets<T>(S: set<set<T>>) {
  forall ss :: ss in S ==> |ss| == 1
}

ghost function U<T> (S : set<set<T>>) : set<T>
  // requires AllSingletonSets(S)
  ensures AllIn(S, U(S))
{
  if S == {} then 
    {}
  else
    var s := pick (S);
    var result := U (S - {s}) + s;
    assert S - {s} + {s} == S;
    result
} 

ghost function pick<T> (s : set<T>) : T
  requires s != {}
{
 var x :| x in s;
 x
}
}