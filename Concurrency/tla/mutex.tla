------------------------------- MODULE mutex -------------------------------
EXTENDS Integers, FiniteSets, Sequences, TLC
CONSTANTS threadcount, maxiterations
ASSUME threadcount \in Nat
ASSUME maxiterations \in Nat
(*--algorithm mutex
\* https://disco.ethz.ch/courses/podc_allstars/lecture/chapter5.pdf
\* Algorithm 5.3 Mutual Exclusion: Test-and-Set
variables
  R = 0,
  X = 0;
fair process thread \in 1..threadcount
variables
  t = -1,
  x = -1,
  iterations = 0
begin
  Outer:
  while iterations < maxiterations do
    Entry: 
      t := R;
      R := 1;
      if (t = 1) then
        goto Entry;
      end if;
    CriticalSectionRead:
      x := X;
    CriticalSectionWrite:
      X := x + 1;
    Exit:
      R := 0;
      iterations := iterations + 1
  end while;
end process
end algorithm
*)
\* BEGIN TRANSLATION
VARIABLES R, X, pc, t, x, iterations

vars == << R, X, pc, t, x, iterations >>

ProcSet == (1..threadcount)

Init == (* Global variables *)
        /\ R = 0
        /\ X = 0
        (* Process thread *)
        /\ t = [self \in 1..threadcount |-> -1]
        /\ x = [self \in 1..threadcount |-> -1]
        /\ iterations = [self \in 1..threadcount |-> 0]
        /\ pc = [self \in ProcSet |-> "Outer"]

Outer(self) == /\ pc[self] = "Outer"
               /\ IF iterations[self] < maxiterations
                     THEN /\ pc' = [pc EXCEPT ![self] = "Entry"]
                     ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
               /\ UNCHANGED << R, X, t, x, iterations >>

Entry(self) == /\ pc[self] = "Entry"
               /\ t' = [t EXCEPT ![self] = R]
               /\ R' = 1
               /\ IF (t'[self] = 1)
                     THEN /\ pc' = [pc EXCEPT ![self] = "Entry"]
                     ELSE /\ pc' = [pc EXCEPT ![self] = "CriticalSectionRead"]
               /\ UNCHANGED << X, x, iterations >>

CriticalSectionRead(self) == /\ pc[self] = "CriticalSectionRead"
                             /\ x' = [x EXCEPT ![self] = X]
                             /\ pc' = [pc EXCEPT ![self] = "CriticalSectionWrite"]
                             /\ UNCHANGED << R, X, t, iterations >>

CriticalSectionWrite(self) == /\ pc[self] = "CriticalSectionWrite"
                              /\ X' = x[self] + 1
                              /\ pc' = [pc EXCEPT ![self] = "Exit"]
                              /\ UNCHANGED << R, t, x, iterations >>

Exit(self) == /\ pc[self] = "Exit"
              /\ R' = 0
              /\ iterations' = [iterations EXCEPT ![self] = iterations[self] + 1]
              /\ pc' = [pc EXCEPT ![self] = "Outer"]
              /\ UNCHANGED << X, t, x >>

thread(self) == Outer(self) \/ Entry(self) \/ CriticalSectionRead(self)
                   \/ CriticalSectionWrite(self) \/ Exit(self)

Next == (\E self \in 1..threadcount: thread(self))
           \/ (* Disjunct to prevent deadlock on termination *)
              ((\A self \in ProcSet: pc[self] = "Done") /\ UNCHANGED vars)

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in 1..threadcount : WF_vars(thread(self))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION
ReduceSet(op(_, _), set, acc) ==
  LET f[s \in SUBSET set] == \* here's where the magic is
    IF s = {} THEN acc
    ELSE LET z == CHOOSE z \in s: TRUE
         IN op(z, f[s \ {z}])
  IN f[set]
ReduceSeq(op(_, _), seq, acc) == ReduceSet(LAMBDA i, a: op(seq[i], a), DOMAIN seq, acc)
add(a,b) == a+b
CriticalThreads == {y \in 1..threadcount : pc[y] = "CriticalSectionRead" \/ pc[y] = "CriticalSectionWrite"}
MutualExclusion == Cardinality(CriticalThreads) <= 1
xisgood == <>[](X = ReduceSeq(add, iterations, 0))
=============================================================================
\* Modification History
\* Last modified Fri Aug 21 15:06:12 PDT 2020 by aaron
\* Last modified Thu Aug 20 17:10:27 PDT 2020 by terranceford
\* Created Thu Aug 20 16:40:37 PDT 2020 by terranceford
