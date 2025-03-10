
module ConcurrencyLiveness {
    type Process(==) = int  // Philosopher
    const P: set<Process>  // Fixed set of processes
    datatype CState = Thinking | Hungry | Eating  // Control states

    datatype TSState = TSState(ticket: int, serving: int, cs: map<Process, CState>, t: map<Process, int>)  // Ticket-system state

    // Name is explicit
    predicate TicketIsInUse(s: TSState, i: int)
        requires s.cs.Keys == s.t.Keys == P
    {
        exists p :: p in P && s.cs[p] != Thinking && s.t[p] == i
    }

    predicate Valid(s: TSState)
    {
    && s.cs.Keys == s.t.Keys == P  // Alt. P <= s.cs.Keys && P <= s.t.Keys
    && s.serving <= s.ticket
    && (forall p ::  // ticket help is in range(serving, ticket)
        p in P && s.cs[p] != Thinking
        ==> s.serving <= s.t[p] < s.ticket
    )
    && (forall p, q ::  // No other process can have the ticket number equals to serving
        p in P && q in P && p != q && s.cs[p] != Thinking && s.cs[q] != Thinking
        ==> s.t[p] != s.t[q]
    )
    && (forall p ::  // We are serving the correct ticket number
        p in P && s.cs[p] == Eating
        ==> s.t[p] == s.serving
    )
    && (forall i ::  // Every ticket from serving to ticket is being used
        s.serving <= i < s.ticket
        ==> TicketIsInUse(s, i)
    )
    }

    // Ensures that no two processes are in the same state
    lemma MutualExclusion(s: TSState, p: Process, q: Process)
        requires Valid(s) && p in P && q in P
        requires s.cs[p] == Eating && s.cs[q] == Eating
        ensures p == q
    {}

    // Possible initial states
    predicate Init(s: TSState)
    {
        && s.cs.Keys == s.t.Keys == P
        && s.ticket == s.serving
        && (forall p ::
            p in P
            ==> s.cs[p] == Thinking)
    }

    // Possible transitions from one state to the next
    predicate Next(s: TSState, s': TSState)
    {
        && Valid(s)
        && (exists p ::
            p in P && NextP(s, p, s')
        )
    }

    // Process p may take an atomic step from s to s'
    predicate NextP(s: TSState, p: Process, s': TSState)
        requires Valid(s) && p in P
    {
        Request(s, p, s') || Enter(s, p, s') || Leave(s, p, s')
    }

    // Need to assert something to help that lemma, related to the TicketIsInUse
    // Invariance of Valid(TSState)
    /*lemma Invariance(s: TSState, s': TSState)
    ensures Init(s) ==> Valid(s)
    ensures Valid(s) ==> && Next(s, s') ==> Valid(s')
    {
    
    }*/

    predicate Request(s: TSState, p: Process, s': TSState)
        requires Valid(s) && p in P
    {
        && s.cs[p] == Thinking
        && s'.ticket == s.ticket + 1
        && s'.serving == s.serving
        && s'.t == s.t[p := s.ticket]
        && s'.cs == s.cs[p := Hungry]
    }

    predicate Enter(s: TSState, p: Process, s': TSState)
        requires Valid(s) && p in P
    {
        && s.cs[p] == Hungry
        && s'.ticket == s.ticket
        && s'.serving == s.serving
        && s'.t == s.t
        && ((s.t[p] == s.serving && s'.cs == s.cs[p := Eating]) ||
            (s.t[p] != s.serving && s'.cs == s.cs))
    }

    predicate Leave(s: TSState, p: Process, s': TSState)
        requires Valid(s) && p in P
    {
        && s.cs[p] == Eating
        && s'.ticket == s.ticket
        && s'.serving == s.serving + 1
        && s'.t == s.t
        && s'.cs == s.cs[p := Thinking]
    }

    // Schedules and traces
    type Schedule = nat-> Process
    type Trace = nat -> TSState

    // A Schedule is a function from times to processes
    ghost predicate IsSchedule(schedule: Schedule)
    {
        forall i :: schedule(i) in P
    }

    // A Trace is a function from times to ticket-system states
    // Basically, we check that the Trace starts in a correct Init
    // and that every pair of consecutive states are allowed (atomic)
    ghost predicate IsTrace(trace: Trace, schedule: Schedule)
        requires IsSchedule(schedule)
    {
        && Init(trace(0))
        && (forall i: nat ::
            Valid(trace(i)) && NextP(trace(i), schedule(i), trace(i + 1))
        )
    }

    // Well, there is always a bigger fish
    ghost predicate HasNext(schedule: Schedule, p: Process, n: nat)
    {
        exists n' :: n <= n' && schedule(n') == p
    }

    // Fairness := for any process p, no matter the steps, there is a time where p will be scheduled
    ghost predicate FairSchedule(schedule: Schedule)
    {
        && IsSchedule(schedule)
        && (forall p, n ::
            p in P
            ==> HasNext(schedule, p, n)
        )
    }

    // Explicit title
    function CurrentlyServedProcess(s: TSState): Process
        requires Valid(s) && exists p :: p in P && s.cs[p] == Hungry
    {
        assert TicketIsInUse(s, s.serving);
        var q :| q in P && s.cs[q] != Thinking && s.t[q] == s.serving;
        q
    }

    lemma GetNextStep(trace: Trace, schedule: Schedule, p: Process, n: nat) returns (n': nat)
        requires FairSchedule(schedule) && IsTrace(trace, schedule) && p in P
        //p is not thinking and is currently being served
        //could be hungry or eating
        requires trace(n).cs[p] != Thinking && trace(n).t[p] == trace(n).serving
        //we find a where p is scheduled
        ensures n <= n' && schedule(n') == p
        //p remains the same
        //because even if they are hungry, they are not scheduled and so they remain hungry
        ensures trace(n').serving == trace(n).serving
        ensures trace(n').cs[p] == trace(n).cs[p]
        ensures trace(n').t[p] == trace(n).t[p]
        //all currently hungry philosophers remain hungry
        ensures (forall q ::
            q in P && trace(n).cs[q] == Hungry
            ==> trace(n').cs[q] == Hungry && trace(n').t[q] == trace(n).t[q])
    {
        assert HasNext(schedule, p, n);
        var u :| n <= u && schedule(u) == p;
        n' := n;
        while schedule(n') != p
            invariant n' <= u
            invariant trace(n').serving == trace(n).serving
            invariant trace(n').cs[p] == trace(n).cs[p]
            invariant trace(n').t[p] == trace(n).t[p]
            invariant (forall q ::
            q in P && trace(n).cs[q] == Hungry
            ==> trace(n').cs[q] == Hungry && trace(n').t[q] == trace(n).t[q])
        decreases u - n'
        {
            n' := n' + 1;
        }
    }

    lemma Liveness(trace: Trace, schedule: Schedule, p: Process, n: nat) returns (n': nat)
        requires FairSchedule(schedule) && IsTrace(trace, schedule) && p in P
        requires trace(n).cs[p] == Hungry
        ensures n <= n' && trace(n').cs[p] == Eating
    {
        n' := n;
        while true
            invariant n <= n' && trace(n').cs[p] == Hungry
            decreases trace(n').t[p] - trace(n').serving
        {
            // Find the currently served process and follow it out of the kitchen
            var q := CurrentlyServedProcess(trace(n'));
            if trace(n').cs[q] == Hungry {
                n' := GetNextStep(trace, schedule, q, n');
                n' := n' + 1; // Take the step from Hungry to Eating
                if p == q {
                    return;
                }
            }
            n' := GetNextStep(trace, schedule, q, n');
            n' := n' + 1; // Take the step from Eating to Thinking
        }
    }
}