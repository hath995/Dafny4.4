------------------------------- MODULE dekker -------------------------------

EXTENDS TLC, Integers

(*--algorithm dekker

variables 
  flag = <<FALSE, FALSE>>;
  next = 1;
  aux_last_in_cs = 1;

define
  RaceFree ==
      \/ pc[1] # "CS"
      \/ pc[2] # "CS"

  Liveness ==
    /\ <>(pc[1] = "CS")
    /\ <>(pc[2] = "CS")
    
  Alternating == px[aux_last_in_cs] # "CS" 
end define;

fair process thread \in {1, 2}
begin
  P1: flag[self] := TRUE;
  P2: 
    while flag[3 - self] do
      P2_1: 
        if next # self then
          P2_1_1: flag[self] := FALSE;
          P2_1_2: await next = self;
          P2_1_3: flag[self] := TRUE;
        end if;
    end while;
  CS: aux_last_in_cs := self;
  P3: next := 3 - self;
  P4: flag[self] := FALSE;
  P5: goto P1;
end process; 
end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "1e5b548" /\ chksum(tla) = "8670d205")
VARIABLES flag, next, pc

(* define statement *)
RaceFree ==
    \/ pc[1] # "CS"
    \/ pc[2] # "CS"

Liveness ==
  /\ <>(pc[1] = "CS")
  /\ <>(pc[2] = "CS")


vars == << flag, next, pc >>

ProcSet == ({1, 2})

Init == (* Global variables *)
        /\ flag = <<FALSE, FALSE>>
        /\ next = 1
        /\ pc = [self \in ProcSet |-> "P1"]

P1(self) == /\ pc[self] = "P1"
            /\ flag' = [flag EXCEPT ![self] = TRUE]
            /\ pc' = [pc EXCEPT ![self] = "P2"]
            /\ next' = next

P2(self) == /\ pc[self] = "P2"
            /\ IF flag[3 - self]
                  THEN /\ pc' = [pc EXCEPT ![self] = "P2_1"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "CS"]
            /\ UNCHANGED << flag, next >>

P2_1(self) == /\ pc[self] = "P2_1"
              /\ IF next # self
                    THEN /\ pc' = [pc EXCEPT ![self] = "P2_1_1"]
                    ELSE /\ pc' = [pc EXCEPT ![self] = "P2"]
              /\ UNCHANGED << flag, next >>

P2_1_1(self) == /\ pc[self] = "P2_1_1"
                /\ flag' = [flag EXCEPT ![self] = FALSE]
                /\ pc' = [pc EXCEPT ![self] = "P2_1_2"]
                /\ next' = next

P2_1_2(self) == /\ pc[self] = "P2_1_2"
                /\ next = self
                /\ pc' = [pc EXCEPT ![self] = "P2_1_3"]
                /\ UNCHANGED << flag, next >>

P2_1_3(self) == /\ pc[self] = "P2_1_3"
                /\ flag' = [flag EXCEPT ![self] = TRUE]
                /\ pc' = [pc EXCEPT ![self] = "P2"]
                /\ next' = next

CS(self) == /\ pc[self] = "CS"
            /\ TRUE
            /\ pc' = [pc EXCEPT ![self] = "P3"]
            /\ UNCHANGED << flag, next >>

P3(self) == /\ pc[self] = "P3"
            /\ next' = 3 - self
            /\ pc' = [pc EXCEPT ![self] = "P4"]
            /\ flag' = flag

P4(self) == /\ pc[self] = "P4"
            /\ flag' = [flag EXCEPT ![self] = FALSE]
            /\ pc' = [pc EXCEPT ![self] = "P5"]
            /\ next' = next

P5(self) == /\ pc[self] = "P5"
            /\ pc' = [pc EXCEPT ![self] = "P1"]
            /\ UNCHANGED << flag, next >>

thread(self) == P1(self) \/ P2(self) \/ P2_1(self) \/ P2_1_1(self)
                   \/ P2_1_2(self) \/ P2_1_3(self) \/ CS(self) \/ P3(self)
                   \/ P4(self) \/ P5(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in {1, 2}: thread(self))
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in {1, 2} : WF_vars(thread(self))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 

=============================================================================
\* Modification History
\* Last modified Tue May 25 13:49:06 PDT 2021 by aaron
\* Created Tue May 25 13:22:10 PDT 2021 by aaron
