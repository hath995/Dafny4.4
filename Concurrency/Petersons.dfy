

module Petersons2 {
    type Process(==) = int
    datatype PState = Start | Gate | Wait | Critical | Exit  // Process state

    datatype TSState = TSState(turn: int, cs: map<Process, PState>, flags: map<Process, bool>)

    function other(p: Process): Process
    {
        if p == 0 then 1 else 0
    }

    predicate Valid(s: TSState)
    {
        && s.cs.Keys == s.flags.Keys == {0, 1}
        && (s.cs[0] == Critical ==> s.cs[1] != Critical)
        && (s.cs[1] == Critical ==> s.cs[0] != Critical)
        && (s.cs[0] == Critical ==> s.flags[1])
        && (s.cs[1] == Critical ==> s.flags[0])
    }

    lemma MutualExclusion(s: TSState, p: Process, q: Process)
        requires Valid(s) && p in {0, 1} && q in {0, 1}
        requires s.cs[p] == Critical && s.cs[q] == Critical
        ensures p == q
    {}

    predicate Init(s: TSState)
    {
        && s.cs.Keys == s.flags.Keys == {0, 1}
        && s.turn == -1
        && (forall p :: p in {0, 1} ==> s.cs[p] == Start && !s.flags[p])
    }

    predicate Next(s: TSState, s': TSState)
    {
        && Valid(s)
        && (exists p :: p in {0, 1} && NextP(s, p, s'))
    }

    predicate NextP(s: TSState, p: Process, s': TSState)
        requires Valid(s) && p in {0, 1}
    {
        StartToGate(s, p, s') || GateToWait(s, p, s') || WaitToWait(s, p, s') || WaitToCritical(s, p, s') || CriticalToExit(s, p, s') || ExitToStart(s, p, s')
    }

    predicate StartToGate(s: TSState, p: Process, s': TSState)
        requires Valid(s) && p in {0, 1}
    {
        && s.cs[p] == Start
        && s'.cs == s.cs[p := Gate]
        && s'.flags == s.flags[p := true]
        && s'.turn == s.turn
    }

    predicate GateToWait(s: TSState, p: Process, s': TSState)
        requires Valid(s) && p in {0, 1}
    {
        && s.cs[p] == Gate
        && s'.cs == s.cs[p := Wait]
        && s'.flags == s.flags
        && s'.turn == other(p)
    }

    predicate WaitToCritical(s: TSState, p: Process, s': TSState)
        requires Valid(s) && p in {0, 1}
    {
        && s.cs[p] == Wait
        && s'.cs == s.cs[p := Critical]
        && s'.flags == s.flags
        && s'.turn == s.turn
    }

    predicate WaitToWait(s: TSState, p: Process, s': TSState)
        requires Valid(s) && p in {0, 1}
    {
        && s.cs[p] == Wait
        && s'.cs == s.cs
        && s'.flags == s.flags
        && s'.turn == s.turn
    }

    predicate CriticalToExit(s: TSState, p: Process, s': TSState)
        requires Valid(s) && p in {0, 1}
    {
        && s.cs[p] == Critical
        && s'.cs == s.cs[p := Exit]
        && s'.flags == s.flags
        && s'.turn == s.turn
    }

    predicate ExitToStart(s: TSState, p: Process, s': TSState)
        requires Valid(s) && p in {0, 1}
    {
        && s.cs[p] == Exit
        && s'.cs == s.cs[p := Start]
        && s'.flags == s.flags[p := false]
        && s'.turn == s.turn
    }

    type Schedule = nat-> Process
    type Trace = nat -> TSState

    ghost predicate IsSchedule(schedule: Schedule)
    {
        forall i :: schedule(i) in {0, 1}
    }

    ghost predicate IsTrace(trace: Trace, schedule: Schedule)
        requires IsSchedule(schedule)
    {
        && Init(trace(0))
        && (forall i: nat ::
            Valid(trace(i)) && NextP(trace(i), schedule(i), trace(i + 1))
        )
    }

    ghost predicate HasNext(schedule: Schedule, p: Process, n: nat)
    {
        exists n' :: n <= n' && schedule(n') == p
    }
    
    ghost predicate FairSchedule(schedule: Schedule)
    {
        && IsSchedule(schedule)
        && (forall p, n :: p in {0, 1} ==> HasNext(schedule, p, n))
    }
}