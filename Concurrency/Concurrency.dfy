

module Concurrency {
    type Process(==)
    datatype CState = Thinking | Hungry | Eating
    datatype TSState = TSState(
        ticket: int,
        serving: int,
        cs: map<Process, CState>,
        t: map<Process, int>
    )
    type Schedule = nat -> Process
    type Trace = nat -> TSState

    class TicketSystem
    {
        const P: set<Process>
        var ticket: int
        var serving: int
        var cs: map<Process, CState>
        var t: map<Process, int>

        predicate Valid()
            reads this
        {
            cs.Keys == t.Keys == P &&
            serving <= ticket &&
            (forall p :: p in P && cs[p] != Thinking ==> serving <= t[p] < ticket) &&
            (forall p,q ::
            p in P && q in P && p != q && cs[p] != Thinking && cs[q] != Thinking
            ==> t[p] != t[q]) &&
            (forall p :: p in P && cs[p] == Eating ==> t[p] == serving)
        }

        constructor (processes: set<Process>)
            ensures Valid()
            ensures P == processes
        {
            P := processes;
            ticket, serving := 0, 0;
            cs := map p | p in processes :: Thinking;
            t := map p | p in processes :: 0;
        }

        lemma MutualExclusion(p: Process, q: Process)
            requires Valid() && p in P && q in P
            requires cs[p] == Eating && cs[q] == Eating
            ensures p == q
        {
        }

        method Request(p: Process)
            requires Valid() && p in P && cs[p] == Thinking
            modifies this
            ensures Valid()
        {
            t, ticket := t[p := ticket], ticket + 1;
            cs := cs[p := Hungry];
        }

        method Enter(p: Process)
            requires Valid() && p in P && cs[p] == Hungry
            modifies this
            ensures Valid()
        {
            if t[p] == serving {
                cs := cs[p := Eating];
            }
        }

        method Leave(p: Process)
            requires Valid() && p in P && cs[p] == Eating
            modifies this
            ensures Valid()
        {
            serving := serving + 1;
            cs := cs[p := Thinking];
        }

        method Enter0(p: Process)
            requires Valid() && p in P && cs[p] == Hungry && t[p] == serving
            modifies this
            ensures Valid()
        {
            cs := cs[p := Eating];
        }

        method Enter1(p: Process)
            requires Valid() && p in P && cs[p] == Hungry && t[p] != serving
            modifies this
            ensures Valid()
        {
        }
        
        method Run(processes: set<Process>)
            requires processes != {}
            decreases *
        {
            var ts := new TicketSystem(processes);
            while true
            invariant ts.Valid()
            decreases *
            {
                var p :| p in ts.P;
                match ts.cs[p] {
                    case Thinking => ts.Request(p);
                    case Hungry => ts.Enter(p);
                    case Eating => ts.Leave(p);
                }
            }
        }

        method Run2(processes: set<Process>)
            requires processes != {}
            decreases *
        {
            var ts := new TicketSystem(processes);
            while true
            invariant ts.Valid()
            decreases *
            {
                var p :| p in ts.P;
                match ts.cs[p] {
                    case Thinking => ts.Request(p);
                    case Hungry =>
                        if ts.t[p] == ts.serving {
                            ts.Enter0(p);
                        } else {
                            ts.Enter1(p);
                        }
                    case Eating => ts.Leave(p);
                }
            }
        }

        method Run3(processes: set<Process>)
            requires processes != {}
            decreases *
        {
            var ts := new TicketSystem(processes);
            while exists p :: p in ts.P && (ts.cs[p] == Hungry ==> ts.t[p] == ts.serving)
                invariant ts.Valid()
                decreases *
            {
                var p :| p in ts.P && (ts.cs[p] == Hungry ==> ts.t[p] == ts.serving);
                match ts.cs[p] {
                    case Thinking => ts.Request(p);
                    case Hungry => ts.Enter0(p);
                    case Eating => ts.Leave(p);
                }
            }
        }

        method RunWithTrace(processes: set<Process>)
            requires processes != {}
            decreases *
        {
            var ts := new TicketSystem(processes);
            var schedule: seq<Process> := [];
            while exists p :: p in ts.P && (ts.cs[p] == Hungry ==> ts.t[p] == ts.serving)
                invariant ts.Valid()
                decreases *
            {
                var p :| p in ts.P && (ts.cs[p] == Hungry ==> ts.t[p] == ts.serving);
                schedule := schedule + [p];
                match ts.cs[p] {
                    case Thinking => ts.Request(p);
                    case Hungry => ts.Enter0(p);
                    case Eating => ts.Leave(p);
                }
            }
        }

        method RunFromSchedule(processes: set<Process>, schedule: nat -> Process)
            requires processes != {}
            requires forall n :: schedule(n) in processes
            decreases *
        {
            var ts := new TicketSystem(processes);
            var n := 0;

            while true
            invariant ts.Valid()
            decreases *  // Omits termination checks
            {
                var p := schedule(n);
                match ts.cs[p] {
                    case Thinking => ts.Request(p);
                    case Hungry => ts.Enter(p);
                    case Eating => ts.Leave(p);
                }
                n := n + 1;
            }
        }
    }
}
