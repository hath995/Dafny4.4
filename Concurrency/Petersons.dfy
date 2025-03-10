

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
        && s.cs[0] in {Start, Gate, Wait, Critical, Exit}
        && s.cs[1] in {Start, Gate, Wait, Critical, Exit}
        && (s.cs[0] in {Gate, Wait, Critical} ==> s.flags[0])
        && (s.cs[1] in {Gate, Wait, Critical} ==> s.flags[1])
        && (s.cs[0] in {Start, Exit} ==> !s.flags[0])
        && (s.cs[1] in {Start, Exit} ==> !s.flags[1])
        && s.turn in {-1, 0, 1}
    }

    lemma MutualExclusion(s: TSState, p: Process, q: Process)
        requires Valid(s)
        requires p in {0, 1}
        requires q in {0, 1}
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
        && (s.turn == p || !s.flags[other(p)])
    }

    predicate WaitToWait(s: TSState, p: Process, s': TSState)
        requires Valid(s) && p in {0, 1}
    {
        && s.cs[p] == Wait
        && s'.cs == s.cs
        && s'.flags == s.flags
        && s.flags[other(p)]
        && s.turn == other(p)
        && s'.turn == s.turn
    }

    predicate CriticalToExit(s: TSState, p: Process, s': TSState)
        requires Valid(s) && p in {0, 1}
    {
        && s.cs[p] == Critical
        && s'.cs == s.cs[p := Exit]
        && s'.flags == s.flags[p := false]
        && s'.turn == s.turn
    }

    predicate ExitToStart(s: TSState, p: Process, s': TSState)
        requires Valid(s) && p in {0, 1}
    {
        && s.cs[p] == Exit
        && s'.cs == s.cs[p := Start]
        && s'.flags == s.flags
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

    lemma GetNextStepOnTurn(trace: Trace, schedule: Schedule, p: Process, n: nat) returns (n': nat)
        requires FairSchedule(schedule) && IsTrace(trace, schedule) && p in {0, 1}
        requires trace(n).turn == other(p)
        requires trace(n).cs[p] == Wait
        ensures n <= n' && trace(n').cs[p] == Wait
        ensures schedule(n') == p
    {
        n' := n;
        assert HasNext(schedule, p, n);
        var u :| n <= u && schedule(u) == p;
        while schedule(n') != p
            invariant n' <= u
            invariant trace(n').cs[p] == Wait
            decreases u - n'
        {
            n' := n' + 1;
        }
    }

    lemma WaitImplies(trace: Trace, schedule: Schedule, p: Process, n: nat)
        requires FairSchedule(schedule) && IsTrace(trace, schedule) && p in {0, 1}
        requires trace(n).cs[p] == Wait
        ensures n >= 2
        ensures exists n_:nat :: n_ < n && trace(n_).cs[p] == Gate
    {
        if n == 2 {
            if schedule(0) == other(p) {
                assert trace(0).cs[p] == Start;
                assert trace(1).cs[p] == Start;
                assert trace(1).cs[other(p)] == Gate;
                if schedule(1) == other(p) {
                    assert trace(2).cs[other(p)] == Gate;
                    assert trace(2).cs[p] == Start;
                }
                assert false;
            }
            assert schedule(0) == p;
            assert schedule(1) == p;
            assert exists n_:nat :: n_ < 2 && trace(n_).cs[p] == Gate;
        }else if n > 2 {
            if trace(n-1).cs[p] == Gate {
                assert exists n_:nat :: n_ < n && trace(n_).cs[p] == Gate;
            }else{
                WaitImplies(trace, schedule, p, n-1);
                assert exists n_:nat :: n_ < n && trace(n_).cs[p] == Gate;
            }
        }else{
            assert false;
        }
    }

    lemma AfterInit(trace: Trace, schedule: Schedule, p: Process, n: nat)
        requires FairSchedule(schedule) && IsTrace(trace, schedule) && p in {0, 1}
        requires n > 2
        ensures trace(n).turn in {0, 1}
    {
        if n == 3 { 
            if schedule(0) == p {
                assert trace(0).cs[p] == Start;
                if schedule(1) == p {
                    assert trace(1).cs[p] == Gate;
                    assert trace(2).turn == other(p);
                }else{
                    assert trace(1).cs[p] == Gate;
                    assert trace(2).cs[other(p)] == Gate;
                }
            }else{
                assert schedule(0) == other(p);
                if schedule(1) == p {
                    assert trace(1).cs[other(p)] == Gate;
                    assert trace(2).cs[other(p)] == Gate;
                }else{
                    assert trace(2).cs[other(p)] == Wait;
                }
            }
        }else if n > 3 {
            AfterInit(trace, schedule, p, n-1);
            assert trace(n-1).turn in {0, 1};
            if schedule(n-1) == p && trace(n-1).cs[p] == Gate {
                assert trace(n).turn == other(p);
            }else if schedule(n-1) == other(p) && trace(n-1).cs[other(p)] == Gate {
                assert trace(n).turn == p;
            }else{
                if schedule(n-1) == p {
                    assert trace(n-1).cs[p] == Start || trace(n-1).cs[p] == Wait || trace(n-1).cs[p] == Critical || trace(n-1).cs[p] == Exit;
                    assert trace(n).turn == trace(n-1).turn;
                }else{
                    assert schedule(n-1) == other(p);
                    assert trace(n-1).cs[other(p)] == Start || trace(n-1).cs[other(p)] == Wait || trace(n-1).cs[other(p)] == Critical || trace(n-1).cs[other(p)] == Exit;
                    assert trace(n).turn == trace(n-1).turn;
                }
                assert trace(n).turn == trace(n-1).turn;
            }

        }else{

        }
    }

    lemma LivenessOnTurn(trace: Trace, schedule: Schedule, p: Process, n: nat) returns (n': nat)
        requires FairSchedule(schedule) && IsTrace(trace, schedule) && p in {0, 1}
        requires schedule(n) == p
        requires trace(n).cs[p] == Wait
        requires trace(n).turn == p
        ensures n <= n' && trace(n').cs[p] == Critical
    {
        assert WaitToCritical(trace(n), p, trace(n+1));
        return n+1;
    }
    
    lemma LivenessOnOther(trace: Trace, schedule: Schedule, p: Process, n: nat) returns (n': nat)
        requires FairSchedule(schedule) && IsTrace(trace, schedule) && p in {0, 1}
        requires schedule(n) == p
        requires trace(n).cs[p] == Wait
        requires trace(n).turn == other(p) && !trace(n).flags[other(p)]
        ensures n <= n' && trace(n').cs[p] == Critical
    {
        assert WaitToCritical(trace(n), p, trace(n+1));
        return n+1;
    }

    lemma getNextStep(trace: Trace, schedule: Schedule, p: Process, n: nat) returns (n': nat)
        requires FairSchedule(schedule) && IsTrace(trace, schedule) && p in {0, 1}
        // requires schedule(n) != p
        // requires trace(n).turn == other(p)
        ensures n <= n' && trace(n').cs[p] == trace(n).cs[p]
        ensures forall i :: n < i < n' ==> schedule(i) != p
        ensures schedule(n') == p
    {
        n' := n;
        assert HasNext(schedule, p, n);
        var u :| n <= u && schedule(u) == p;
        while schedule(n') != p
            invariant n' <= u
            invariant trace(n').cs[p] == trace(n).cs[p]
            invariant forall i :: n <= i < n' ==> schedule(i) != p
            decreases u - n'
        {
            n' := n' + 1;
        }
    }

    lemma WaitContinuity(trace: Trace, schedule: Schedule, p: Process, n: nat, u: nat)
        requires FairSchedule(schedule) && IsTrace(trace, schedule) && p in {0, 1}
        requires trace(n).cs[p] == Wait
        requires u > n
        requires forall i :: n <= i < u ==> schedule(i) != p
        ensures trace(n).cs[p] == Wait
    {
    }

    lemma WaitContinuity2(trace: Trace, schedule: Schedule, p: Process, n: nat, u: nat)
        requires FairSchedule(schedule) && IsTrace(trace, schedule) && p in {0, 1}
        requires trace(n).flags[other(p)]
        requires trace(n).turn == other(p)
        requires trace(n).cs[p] == Wait
        requires u > n
        requires forall i :: n <= i < u ==> schedule(i) == p
        ensures trace(u).cs[p] == Wait
    {
        var n' := n;
        while n' < u
            invariant n <= n' <= u
            invariant forall i :: n <= i < n' ==> schedule(i) == p
            invariant trace(n').flags[other(p)]
            invariant trace(n').turn == other(p)
            invariant trace(n').cs[p] == Wait
            decreases u - n'
        {
            n' := n' + 1;
        }
    }

    // https://imgur.com/gallery/well-were-waiting-intergalactic-quality-upgrade-q48zWbR
    lemma {:isolate_assertion} BothWaiting(trace: Trace, schedule: Schedule, p: Process, n: nat) returns (n': nat)
        requires FairSchedule(schedule) && IsTrace(trace, schedule) && p in {0, 1}
        requires trace(n).cs[p] == Wait
        requires trace(n).cs[other(p)] == Wait
        requires trace(n).turn == p
        ensures n <= n' 
        ensures forall i :: n <= i < n' ==> schedule(i) != p
        ensures trace(n').turn == p
        ensures trace(n').cs[p] == Wait
    {
        var u := getNextStep(trace, schedule, p, n);
        n' := n;
        while n' < u
            invariant n <= n' <= u
            invariant forall i :: n < i < n' ==> schedule(i) != p
            invariant trace(n').cs[other(p)] == Wait
            invariant trace(n').cs[p] == Wait
            decreases u - n'
        {
            n' := n' + 1;
        }
    }

    lemma LivenessOnSchedule(trace: Trace, schedule: Schedule, p: Process, n: nat) returns (n': nat)
        requires FairSchedule(schedule) && IsTrace(trace, schedule) && p in {0, 1}
        requires schedule(n) == p
        requires trace(n).turn == other(p)
        requires trace(n).flags[other(p)]
        requires trace(n).cs[p] == Wait
        ensures n <= n' && trace(n').cs[p] == Critical
    {
            WaitImplies(trace, schedule, p, n);
            AfterInit(trace, schedule, p, n);
            if trace(n).cs[other(p)] == Start || trace(n).cs[other(p)] == Exit {
                assert false;
            }
            assert trace(n).turn == other(p);
            assert trace(n).flags[other(p)];

            var u := getNextStep(trace, schedule, other(p), n);
            assert schedule(u) == other(p);
            if trace(u).cs[other(p)] == Gate {
                assert trace(u+1).cs[other(p)] == Wait;
                WaitContinuity2(trace, schedule, p, n, u);
                assert trace(u+1).cs[p] == Wait;
                assert trace(u+1).turn == p;
                var u' := getNextStep(trace, schedule, p, u);
                n' := LivenessOnTurn(trace, schedule, p, u');
                return n';
            }else if trace(u).cs[other(p)] == Wait {
            }else if trace(u).cs[other(p)] == Critical {
            }else{
                assert false;
            }
    }

    lemma Liveness(trace: Trace, schedule: Schedule, p: Process, n: nat) returns (n': nat)
        requires FairSchedule(schedule) && IsTrace(trace, schedule) && p in {0, 1}
        // requires schedule(n) == p
        requires trace(n).cs[p] == Wait
        ensures n <= n' && trace(n').cs[p] == Critical
    {
        n' := n;
        if schedule(n) == p && trace(n).turn == p {
            n' := LivenessOnTurn(trace, schedule, p, n); 
            return n';
        }else if schedule(n) == p && trace(n).turn == other(p) && !trace(n).flags[other(p)] {
            n' := LivenessOnOther(trace, schedule, p, n);
            return n';
        }else if schedule(n) == p {
            WaitImplies(trace, schedule, p, n);
            AfterInit(trace, schedule, p, n);
            n' := LivenessOnSchedule(trace, schedule, p, n);
            return n';
        } else {
            var u := getNextStep(trace, schedule, p, n);
            if trace(u).turn == other(p) && trace(u).flags[other(p)] {
                n' := LivenessOnSchedule(trace, schedule, p, u);
                return n';
            }else if trace(u).turn == p {
                n' := LivenessOnTurn(trace, schedule, p, u);
                return n';
            }else if trace(u).turn == other(p) && !trace(u).flags[other(p)] {
                n' := LivenessOnOther(trace, schedule, p, u);
                return n';
            }else{
                WaitImplies(trace, schedule, p, u);
                AfterInit(trace, schedule, p, u);
                assert trace(u).turn == -1;
                assert false;
            }
        }
    }
}