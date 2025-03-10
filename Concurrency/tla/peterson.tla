------------------------------ MODULE peterson ------------------------------
EXTENDS Integers, FiniteSets
(*--algorithm petersonsmutex
variables
  flag = <<FALSE, FALSE>>,
  X = 0,
  turn = -1;
define
  other(i) == 3 - i
end define
fair process thread \in 1..2
variables
  x = -1;
begin
  Start:
    flag[self] := TRUE;
  Gate:
    turn := other(self);
  Busy_Wait:
    while flag[other(self)] = TRUE /\ turn = other(self) do
      skip;
    end while;
  Critical_Section_Read:
    x := X;
  Critical_Section_Write:
    X := x + 1;
  Exit:
    flag[self] := FALSE;
end process
end algorithm
*)
\* BEGIN TRANSLATION
VARIABLES flag, X, turn, pc

(* define statement *)
other(i) == 3 - i

VARIABLE x

vars == << flag, X, turn, pc, x >>

ProcSet == (1..2)

Init == (* Global variables *)
        /\ flag = <<FALSE, FALSE>>
        /\ X = 0
        /\ turn = -1
        (* Process thread *)
        /\ x = [self \in 1..2 |-> -1]
        /\ pc = [self \in ProcSet |-> "Start"]

Start(self) == /\ pc[self] = "Start"
               /\ flag' = [flag EXCEPT ![self] = TRUE]
               /\ pc' = [pc EXCEPT ![self] = "Gate"]
               /\ UNCHANGED << X, turn, x >>

Gate(self) == /\ pc[self] = "Gate"
              /\ turn' = other(self)
              /\ pc' = [pc EXCEPT ![self] = "Busy_Wait"]
              /\ UNCHANGED << flag, X, x >>

Busy_Wait(self) == /\ pc[self] = "Busy_Wait"
                   /\ IF flag[other(self)] = TRUE /\ turn = other(self)
                         THEN /\ TRUE
                              /\ pc' = [pc EXCEPT ![self] = "Busy_Wait"]
                         ELSE /\ pc' = [pc EXCEPT ![self] = "Critical_Section_Read"]
                   /\ UNCHANGED << flag, X, turn, x >>

Critical_Section_Read(self) == /\ pc[self] = "Critical_Section_Read"
                               /\ x' = [x EXCEPT ![self] = X]
                               /\ pc' = [pc EXCEPT ![self] = "Critical_Section_Write"]
                               /\ UNCHANGED << flag, X, turn >>

Critical_Section_Write(self) == /\ pc[self] = "Critical_Section_Write"
                                /\ X' = x[self] + 1
                                /\ pc' = [pc EXCEPT ![self] = "Exit"]
                                /\ UNCHANGED << flag, turn, x >>

Exit(self) == /\ pc[self] = "Exit"
              /\ flag' = [flag EXCEPT ![self] = FALSE]
              /\ pc' = [pc EXCEPT ![self] = "Done"]
              /\ UNCHANGED << X, turn, x >>

thread(self) == Start(self) \/ Gate(self) \/ Busy_Wait(self)
                   \/ Critical_Section_Read(self)
                   \/ Critical_Section_Write(self) \/ Exit(self)

Next == (\E self \in 1..2: thread(self))
           \/ (* Disjunct to prevent deadlock on termination *)
              ((\A self \in ProcSet: pc[self] = "Done") /\ UNCHANGED vars)

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in 1..2 : WF_vars(thread(self))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION
CriticalThreads == {y \in 1..2 : pc[y] = "Critical_Section_Read" \/ pc[y] = "Critical_Section_Write"}
MutualExclusion == Cardinality(CriticalThreads) <= 1

=============================================================================
\* Modification History
\* Last modified Mon Aug 31 16:47:38 PDT 2020 by aaron
\* Created Mon Aug 31 16:45:17 PDT 2020 by aaron
