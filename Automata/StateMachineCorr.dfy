include "./NFA.dfy"
include "./StateMachines.dfy"
include "../examples/combinatorics.dfy"

module SMCorr {
    import opened StateMachines
    import opened NFAutomata
    import opened Combinatorics

    ghost predicate MachinesEquivalent<States(!new), StateSets(!new), Alphabet(!new)>(dfa: DFA<StateSets, Alphabet>, nfa: NFA<States, Alphabet>)
        requires dfa.alphabet == nfa.alphabet
        requires ValidDfa(dfa)
        requires ValidNfa(nfa)
    {
        Language(dfa) == NFALanguage(nfa)
    }

    function DfaToNfa<State(!new, ==), Alphabet(!new, ==)>(dfa: DFA<State, Alphabet>): NFA<State, Alphabet>
        requires ValidDfa(dfa)
        ensures ValidNfa(DfaToNfa(dfa))
        ensures forall key :: key in DfaToNfa(dfa).transitions.Keys ==> |DfaToNfa(dfa).transitions[key]| == 1
        ensures DfaToNfa(dfa).transitions == map pair: (State, Alphabet) | pair in Cross(dfa.states, dfa.alphabet) :: {dfa.transition(pair.0, pair.1)} // Each transition maps to a single state
    {
        var transitions := map pair: (State, Alphabet) | pair in Cross(dfa.states, dfa.alphabet) :: {dfa.transition(pair.0, pair.1)};

        NFA(dfa.states, dfa.startState, dfa.acceptStates, dfa.alphabet, transitions, map[])
    }

    function NfaDfaDelta<State(!new, ==), Alphabet(!new, ==)>(nfa: NFA, R: set<State>, a: Alphabet): set<State>
        requires ValidNfa(nfa)
        ensures NfaDfaDelta(nfa, R, a) in set state | state <= nfa.states :: state
    {
        assert {} <= nfa.states;
        if a !in nfa.alphabet || !(R <= nfa.states) then {}
        else
            EpsilonClosure(nfa, Delta(nfa,R, a))
    }

    function NfaToDfa<State(!new), Alphabet(!new)>(nfa: NFA): DFA<set<State>, Alphabet> 
        requires ValidNfa(nfa)
        ensures ValidDfa(NfaToDfa(nfa))
    {
        var result:= DFA(
            set state | state <= nfa.states :: state,
            nfa.alphabet, 
            (state: set<State>, a: Alphabet) => NfaDfaDelta(nfa, state, a),
            EpsilonClosure(nfa, {nfa.startState}),
            set S | S <= nfa.states && S * nfa.acceptStates != {}
            // set accept_state, state | state <= nfa.states && accept_state in nfa.accept_states && accept_state in state :: state
        );
        assert {nfa.startState} <= nfa.states;
        result
    }



lemma NfaExtendedDeltaComputesTrace<State, Alphabet>(nfa: NFA<State, Alphabet>, w: seq<Alphabet>)
    requires ValidNfa(nfa) && NFAutomata.ValidString(nfa, w)
    ensures exists trace: seq<set<State>> :: 
        IsValidNfaTrace(nfa, w, trace) && 
        NfaExtendedDelta(nfa, {nfa.startState}, w) == trace[|w|]
    decreases |w|
{
    if |w| == 0 {
        // Base case: The trace is just one set, the initial epsilon closure.
        var trace0 := [EpsilonClosure(nfa, {nfa.startState})];
        assert IsValidNfaTrace(nfa, [], trace0);
        assert NfaExtendedDelta(nfa, {nfa.startState}, []) == trace0[0];
    } else {
        // Inductive step:
        var prefix := w[..|w|-1];
        var last_char := w[|w|-1];
        // By the IH, there exists a valid trace for the prefix.
        var prefix_trace: seq<set<State>> :| IsValidNfaTrace(nfa, prefix, prefix_trace) &&
                                             NfaExtendedDelta(nfa, {nfa.startState}, prefix) == prefix_trace[|prefix|];
        
        // We construct the full trace by adding one more step.
        var last_state_set := prefix_trace[|prefix|];
        var next_state_set := EpsilonClosure(nfa, Delta(nfa, last_state_set, last_char));
        var full_trace := prefix_trace + [next_state_set];

        // Prove this new trace is valid for `w`.
        assert IsValidNfaTrace(nfa, w, full_trace);
        
        // Prove that NfaExtendedDelta computes the last element of this trace.
        // Unfold the definition of NfaExtendedDelta for `w`.
        var nfa_final_states := NfaExtendedDelta(nfa, {nfa.startState}, w);
        // Its recursive call matches what we have from the IH.
        assert nfa_final_states == next_state_set;
        assert nfa_final_states == full_trace[|w|];
    }
}

// Now, we prove the lemma you were trying to write.
lemma NfaExtendedDeltaAccepting<State(!new), Alphabet(!new)>(nfa: NFA<State, Alphabet>, w: seq<Alphabet>)
    requires ValidNfa(nfa) && NFAutomata.ValidString(nfa, w)
    requires NFAutomata.Accepted(nfa, w) // The premise: the NFA accepts the word.
    ensures var final_states := NfaExtendedDelta(nfa, {nfa.startState}, w);
            final_states * nfa.acceptStates != {}
{
    // 1. From `requires Accepted(nfa, w)`, we know there exists an accepting trace.
    var accepting_trace: seq<set<State>> :| 
        IsValidNfaTrace(nfa, w, accepting_trace) &&
        accepting_trace[|w|] * nfa.acceptStates != {};

    // 2. From our `NfaExtendedDeltaComputesTrace` lemma, we know there also exists
    //    a trace computed by our function.
    NfaExtendedDeltaComputesTrace(nfa, w);
    var computed_trace: seq<set<State>> :|
        IsValidNfaTrace(nfa, w, computed_trace) &&
        NfaExtendedDelta(nfa, {nfa.startState}, w) == computed_trace[|w|];
        
    // 3. We need to prove that any two valid traces for the same NFA and word are identical.
    //    This is because the subset construction is deterministic.
    UniqueNfaTrace(nfa, w, accepting_trace, computed_trace);
    assert accepting_trace == computed_trace;

    // 4. Since the traces are the same, their last elements must be the same.
    assert accepting_trace[|w|] == computed_trace[|w|];
    
    // 5. Therefore, the property of the accepting trace must also hold for the computed trace's last element.
    var final_states := NfaExtendedDelta(nfa, {nfa.startState}, w);
    assert final_states == accepting_trace[|w|];
    assert final_states * nfa.acceptStates != {}; // This is our goal.
}


lemma NFA_DFA_Equivalent<State(!new), Alphabet(!new)>(nfa: NFA<State, Alphabet>)
    requires ValidNfa(nfa)
    ensures Language(NfaToDfa(nfa)) == NFALanguage(nfa)
{
    var dfa := NfaToDfa(nfa);

    forall word | word in NFALanguage(nfa)
        ensures StateMachines.Accepted(dfa, word)
    {
        DfaPathCorrespondsToNfaPath(nfa, word);
        
        var dfa_path := ComputeStateSequence(dfa, word);
        var dfa_final_state := dfa_path[|word|];
        var nfa_final_states := NfaExtendedDelta(nfa, {nfa.startState}, word);
        NfaExtendedDeltaAccepting(nfa, word);
        assert nfa_final_states * nfa.acceptStates != {};
        assert dfa_final_state == nfa_final_states;
        assert StateMachines.Accepted(dfa, word);

    }

    forall word | word in Language(NfaToDfa(nfa)) 
        ensures NFAutomata.Accepted(nfa, word)
    {
        assert StateMachines.Accepted(dfa, word);
        var dfa_path := ComputeStateSequence(dfa, word);
        ComputeStateSequenceAccepting(dfa, word);
        assert IsValidNfaTrace(nfa, word, dfa_path);
        var dfa_final_state := dfa_path[|word|];
        assert dfa_final_state in dfa.acceptStates;
        assert dfa_final_state * nfa.acceptStates != {};
    }
    // Set equality follows from element-wise equivalence.
}

    // For the NFA: computes the set of all possible final states after reading a whole word.
ghost function NfaExtendedDelta<State, Alphabet>(nfa: NFA<State, Alphabet>, S: set<State>, w: seq<Alphabet>) : set<State>
    requires ValidNfa(nfa) && S <= nfa.states && NFAutomata.ValidString(nfa, w)
    decreases |w|
{
    if |w| == 0 then EpsilonClosure(nfa, S)
    else
        var prefix_states := NfaExtendedDelta(nfa, S, w[..|w|-1]);
        var after_symbol := Delta(nfa, prefix_states, w[|w|-1]);
        EpsilonClosure(nfa, after_symbol)
}

lemma DfaPathCorrespondsToNfaPath<State(!new), Alphabet(!new)>(nfa: NFA<State, Alphabet>, w: seq<Alphabet>)
    requires ValidNfa(nfa) && NFAutomata.ValidString(nfa, w)
    ensures var dfa := NfaToDfa(nfa);
            var dfa_path := ComputeStateSequence(dfa, w);
            // The final state of the DFA path...
            dfa_path[|w|] == 
            // ...is equal to the set of all possible NFA states.
            NfaExtendedDelta(nfa, {nfa.startState}, w)
    decreases |w|
{
    var dfa: DFA<set<State>, Alphabet> := NfaToDfa(nfa);

    if |w| == 0 {
        // Base Case: w is empty.
        var dfa_path := ComputeStateSequence(dfa, []);
        assert |dfa_path| == 1;
        // The final state of the DFA is its start state.
        var dfa_final_state := dfa_path[0];
        assert dfa_final_state == dfa.startState;

        // The final set of NFA states is the EpsilonClosure of its start state.
        var nfa_final_states := NfaExtendedDelta(nfa, {nfa.startState}, []);
        assert nfa_final_states == EpsilonClosure(nfa, {nfa.startState});

        // By our corrected NfaToDfa definition, these are equal.
        assert dfa.startState == nfa_final_states;
        assert dfa_final_state == nfa_final_states; // Goal holds.
    } else {
        // Inductive Step: w = prefix + last_char
        var prefix := w[..|w|-1];
        var last_char := w[|w|-1];

        // Apply Induction Hypothesis on the shorter prefix.
        DfaPathCorrespondsToNfaPath(nfa, prefix);
        
        var dfa_prefix_path := ComputeStateSequence(dfa, prefix);
        var dfa_state_after_prefix := dfa_prefix_path[|prefix|];
        var nfa_states_after_prefix := NfaExtendedDelta(nfa, {nfa.startState}, prefix);
        // By the IH, these are equal.
        assert dfa_state_after_prefix == nfa_states_after_prefix;

        // Now, trace the final step for both machines.
        var dfa_full_path := ComputeStateSequence(dfa, w);
        var dfa_final_state := dfa_full_path[|w|];
        // By definition of ComputeStateSequence, the last state is:
        UniqueStateSequence(dfa, w, dfa_full_path, dfa_prefix_path+[dfa.transition(dfa_prefix_path[|w|-1], last_char)]);
        assert dfa_final_state == dfa.transition(dfa_state_after_prefix, last_char);

        // For the NFA, the final set of states is:
        var nfa_final_states := EpsilonClosure(nfa, Delta(nfa, nfa_states_after_prefix, last_char));
        
        // By definition of the DFA's transition function in `NfaToDfa`:
        // dfa.transition(R, a) == EpsilonClosure(nfa, Delta(nfa, R, a))
        // Since dfa_state_after_prefix == nfa_states_after_prefix, the calculations are identical.
        assert dfa_final_state == nfa_final_states;

        // The final state of the DFA path is equal to the final set of NFA states.
        // This is not quite the ensures clause. We need to relate nfa_final_states
        // to NfaExtendedDelta(nfa, {nfa.start_state}, w).
        assert nfa_final_states == NfaExtendedDelta(nfa, {nfa.startState}, w);
        assert dfa_final_state == NfaExtendedDelta(nfa, {nfa.startState}, w);
    }
}

    lemma accept_States<State(!new), Alphabet(!new)>(nfa: NFA)
        requires ValidNfa(nfa)
        ensures (set S | S <= nfa.states && S * nfa.acceptStates != {}) == set accept_state, state | state <= nfa.states && accept_state in nfa.acceptStates && accept_state in state :: state
    {
       var ss := set S | S <= nfa.states && S * nfa.acceptStates != {};
       var ys := set accept_state, state | state <= nfa.states && accept_state in nfa.acceptStates && accept_state in state :: state;
       forall x | x in ss
          ensures x in ys;
       {}

       forall x | x in ys
          ensures x in ss;
       {
        assert x <= nfa.states;
        var ac :| ac in nfa.acceptStates && ac in x; 
        assert ac in x * nfa.acceptStates;
        assert x * nfa.acceptStates != {};
       }
    }

}