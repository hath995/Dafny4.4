------------------------- MODULE peterson_multiple -------------------------
EXTENDS Integers, FiniteSets, Sequences, TLC
CONSTANTS ThreadCount
ASSUME ThreadCount \in Nat
threadSet == 1..ThreadCount
(*--algorithm peterson_multiple

variables level = [j \in threadSet |-> -1], last_to_enter = [j \in threadSet |-> -1], X = 0;

fair process thread \in threadSet
variable x = 0, l = 1;
begin
  start:
    while l <= ThreadCount do
      level[self] := l;
      last_to_enter[l] := self;
      Lock_Wait:
      while last_to_enter[l] = self /\ (\E k \in threadSet : level[k] >= l) do
        skip;
      end while; 
      l := l + 1
    end while;
  Critical_Section_Read:
    x := X;
  Critical_Section_Write:
    X := x + 1;
  Exit:
    level[self] := -1;
end process;

end algorithm;
*)
\* BEGIN TRANSLATION
VARIABLES level, last_to_enter, X, pc, x, l

vars == << level, last_to_enter, X, pc, x, l >>

ProcSet == (threadSet)

Init == (* Global variables *)
        /\ level = [j \in threadSet |-> -1]
        /\ last_to_enter = [j \in threadSet |-> -1]
        /\ X = 0
        (* Process thread *)
        /\ x = [self \in threadSet |-> 0]
        /\ l = [self \in threadSet |-> 1]
        /\ pc = [self \in ProcSet |-> "start"]

start(self) == /\ pc[self] = "start"
               /\ IF l[self] <= ThreadCount
                     THEN /\ level' = [level EXCEPT ![self] = l[self]]
                          /\ last_to_enter' = [last_to_enter EXCEPT ![l[self]] = self]
                          /\ pc' = [pc EXCEPT ![self] = "Lock_Wait"]
                     ELSE /\ pc' = [pc EXCEPT ![self] = "Critical_Section_Read"]
                          /\ UNCHANGED << level, last_to_enter >>
               /\ UNCHANGED << X, x, l >>

Lock_Wait(self) == /\ pc[self] = "Lock_Wait"
                   /\ IF last_to_enter[l[self]] = self /\ (\E k \in threadSet : level[k] >= l[self])
                         THEN /\ TRUE
                              /\ pc' = [pc EXCEPT ![self] = "Lock_Wait"]
                              /\ l' = l
                         ELSE /\ l' = [l EXCEPT ![self] = l[self] + 1]
                              /\ pc' = [pc EXCEPT ![self] = "start"]
                   /\ UNCHANGED << level, last_to_enter, X, x >>

Critical_Section_Read(self) == /\ pc[self] = "Critical_Section_Read"
                               /\ x' = [x EXCEPT ![self] = X]
                               /\ pc' = [pc EXCEPT ![self] = "Critical_Section_Write"]
                               /\ UNCHANGED << level, last_to_enter, X, l >>

Critical_Section_Write(self) == /\ pc[self] = "Critical_Section_Write"
                                /\ X' = x[self] + 1
                                /\ pc' = [pc EXCEPT ![self] = "Exit"]
                                /\ UNCHANGED << level, last_to_enter, x, l >>

Exit(self) == /\ pc[self] = "Exit"
              /\ level' = [level EXCEPT ![self] = -1]
              /\ pc' = [pc EXCEPT ![self] = "Done"]
              /\ UNCHANGED << last_to_enter, X, x, l >>

thread(self) == start(self) \/ Lock_Wait(self)
                   \/ Critical_Section_Read(self)
                   \/ Critical_Section_Write(self) \/ Exit(self)

Next == (\E self \in threadSet: thread(self))
           \/ (* Disjunct to prevent deadlock on termination *)
              ((\A self \in ProcSet: pc[self] = "Done") /\ UNCHANGED vars)

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in threadSet : WF_vars(thread(self))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION
CriticalThreads == {y \in 1..2 : pc[y] = "Critical_Section_Read" \/ pc[y] = "Critical_Section_Write"}
MutualExclusion == Cardinality(CriticalThreads) <= 1
Exception == ~(\A self \in ProcSet: pc[self] = "Lock_Wait")
=============================================================================
\* Modification History
\* Last modified Tue Sep 01 17:38:16 PDT 2020 by aaron
\* Created Tue Sep 01 16:45:17 PDT 2020 by aaron
