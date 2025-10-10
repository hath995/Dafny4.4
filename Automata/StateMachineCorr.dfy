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

    lemma DfaNfaDeltaHasSingleResult<State(!new, ==), Alphabet(!new, ==)>(dfa: DFA<State, Alphabet>, R: set<State>, a: Alphabet)
        requires ValidDfa(dfa)
        requires R <= dfa.states
        requires a in dfa.alphabet

        requires |R| == 1
        ensures |Delta(DfaToNfa(dfa), R, a)| == 1
        ensures EpsilonClosure(DfaToNfa(dfa), Delta(DfaToNfa(dfa), R, a)) == Delta(DfaToNfa(dfa), R, a)
    {
        assert R != {};
        var s :| s in R;
        assert |R-{s}| == 0;
        assert s in dfa.states;
        assert (s, a) in DfaToNfa(dfa).transitions;
        assert Delta(DfaToNfa(dfa), R, a) == {dfa.transition(s, a)};
        assert |Delta(DfaToNfa(dfa), R, a)| == 1;
        EpsilonClosureWithNoEpsilons(DfaToNfa(dfa), Delta(DfaToNfa(dfa), R, a));
    }

    lemma AreTransitionsOfDfaToNfa<State(!new, ==), Alphabet(!new, ==)>(dfa: DFA<State, Alphabet>, word: seq<Alphabet>, dfa_path: seq<State>, i: int)
        requires ValidDfa(dfa)
        requires StateMachines.ValidString(dfa, word)
        requires dfa_path == ComputeStateSequence(dfa, word)
        requires 0 <= i < |word|
        ensures {dfa_path[i+1]} == Delta(DfaToNfa(dfa), {dfa_path[i]}, word[i])
    {
        DfaNfaDeltaHasSingleResult(dfa, {dfa_path[i]}, word[i]);
    }

    lemma NfaSequenceOfDfa<State(!new, ==), Alphabet(!new, ==)>(dfa: DFA<State, Alphabet>, word: seq<Alphabet>, nfa_path: seq<set<State>>, i: int)
        requires ValidDfa(dfa)
        requires StateMachines.ValidString(dfa, word)
        requires NFAutomata.Accepted(DfaToNfa(dfa), word)
        requires IsValidNfaTrace(DfaToNfa(dfa), word, nfa_path)
        requires NfaExtendedDelta(DfaToNfa(dfa), {dfa.startState}, word) == nfa_path[|word|]
        requires 0 <= i <= |word|
        ensures |nfa_path[i]| == 1
        // ensures seq(|word|+1, i requires 0 <= i < |word|+1 => {ComputeStateSequence(dfa, word)[i]}) == ComputeStateSequence(DfaToNfa(dfa), word)
    {
        if i == 0 {
            assert nfa_path[0] == EpsilonClosure(DfaToNfa(dfa), {dfa.startState});
            assert dfa.startState in nfa_path[0];
            assert |nfa_path[0]| == 1;
        } else {
           NfaSequenceOfDfa(dfa, word, nfa_path, i-1); 
           DfaNfaDeltaHasSingleResult(dfa, nfa_path[i-1], word[i-1]);
        }
    }

    ghost function Pick<T>(s: set<T>): T
        requires s != {}
        ensures Pick(s) in s
    {
        var x :| x in s;
        x
    }

    lemma NfaSequenceOfDfa2<State(!new, ==), Alphabet(!new, ==)>(dfa: DFA<State, Alphabet>, word: seq<Alphabet>, nfa_path: seq<set<State>>, dfa_path: seq<State>, i: int)
        requires ValidDfa(dfa)
        requires StateMachines.ValidString(dfa, word)
        requires NFAutomata.Accepted(DfaToNfa(dfa), word)
        requires IsValidNfaTrace(DfaToNfa(dfa), word, nfa_path)
        requires NfaExtendedDelta(DfaToNfa(dfa), {dfa.startState}, word) == nfa_path[|word|]
        requires 0 <= i < |word|
        requires forall i :: 0 <= i <= |word| ==> |nfa_path[i]| == 1
        requires dfa_path == seq(|word|+1, i requires 0 <= i < |word|+1 => Pick(nfa_path[i]));
        ensures dfa_path[i+1] == dfa.transition(dfa_path[i], word[i])
    {
        if i == 0 {
            assert nfa_path[0] == EpsilonClosure(DfaToNfa(dfa), {dfa.startState});
            EpsilonClosureWithNoEpsilons(DfaToNfa(dfa), nfa_path[0]);
            assert nfa_path[0] == {dfa.startState};
            assert dfa_path[0] == dfa.startState;
            assert nfa_path[0] == {dfa.startState};
            assert nfa_path[1] == EpsilonClosure(DfaToNfa(dfa), {dfa.transition(dfa.startState, word[0])});
            EpsilonClosureWithNoEpsilons(DfaToNfa(dfa), {dfa.transition(dfa.startState, word[0])});

            assert dfa_path[1] == dfa.transition(dfa.startState, word[0]);

        }else{
            var q := dfa.transition(dfa_path[i-1], word[i-1]);
            NfaSequenceOfDfa2(dfa, word, nfa_path, dfa_path, i-1);
            assert q in nfa_path[i];
            assert |nfa_path[i]-{q}| == 0;
            assert nfa_path[i]  =={dfa.transition(dfa_path[i-1], word[i-1])};
            EpsilonClosureWithNoEpsilons(DfaToNfa(dfa), {dfa.transition(dfa_path[i-1], word[i-1])});
            // EpsilonClosureWithNoEpsilons(DfaToNfa(dfa), nfa_path[i]);
            assert dfa_path[i+1] == dfa.transition(dfa_path[i], word[i]);
        }
    }

    lemma {:isolate_assertions} DFA_NFA_Equivalent<State(!new, ==), Alphabet(!new, ==)>(dfa: DFA<State, Alphabet>)
        requires ValidDfa(dfa)
        ensures Language(dfa) == NFALanguage(DfaToNfa(dfa))
    {
        var nfa := DfaToNfa(dfa);
        assert ValidNfa(nfa);
        assert dfa.alphabet == nfa.alphabet;

        forall word | word in Language(dfa)
            ensures NFAutomata.Accepted(nfa, word)
        {
            ComputeStateSequenceAccepting(dfa, word);
            var dfa_path := ComputeStateSequence(dfa, word);
            var dfa_final_state: State := dfa_path[ |word| ];
            assert dfa_final_state in dfa.acceptStates;
            var nfa_path := seq(|word|+1, i requires 0 <= i < |word|+1 => {dfa_path[i]});
            assert dfa_path[0] == dfa.startState;
            assert nfa_path[0] == EpsilonClosure(nfa, {nfa.startState});
            forall i | 0 <= i < |word| 
              ensures nfa_path[i] <= nfa.states && NfaTransitionStep(nfa, nfa_path[i], word[i], nfa_path[i+1])
            {
                AreTransitionsOfDfaToNfa(dfa, word, dfa_path, i);
            }
            assert IsValidNfaTrace(nfa, word, nfa_path);
            assert nfa.acceptStates == dfa.acceptStates;
            assert dfa_final_state in nfa.acceptStates;
            assert nfa_path[|word|] == {dfa_final_state};
            assert dfa_final_state in {dfa_final_state};
            assert dfa_final_state in ({dfa_final_state} * nfa.acceptStates);
            assert {dfa_final_state} * nfa.acceptStates != {};
            assert nfa_path[|word|] * nfa.acceptStates != {};
            // assert dfa_final_state * nfa.acceptStates != {};
        }

        forall word | word in NFALanguage(nfa)
            ensures StateMachines.Accepted(dfa, word)
        {
            assert NFAutomata.Accepted(nfa, word);
            NfaExtendedDeltaComputesTrace(nfa, word);
            NfaExtendedDeltaAccepting(nfa, word);
            var nfa_path :| IsValidNfaTrace(nfa, word, nfa_path) &&
                            NfaExtendedDelta(nfa, {nfa.startState}, word) == nfa_path[|word|];
            assert nfa_path[|word|] * nfa.acceptStates != {};
            var nfa_final_states := nfa_path[|word|];
            assert nfa_final_states * nfa.acceptStates != {};
            forall i | 0 <= i <= |word| 
                ensures |nfa_path[i]| == 1
            {
                NfaSequenceOfDfa(dfa, word, nfa_path, i);
            }
            var dfa_path := seq(|word|+1, i requires 0 <= i < |word|+1 => Pick(nfa_path[i]));
            assert dfa_path[0] == dfa.startState;
            forall i | 1 <= i < |word| 
                ensures dfa_path[i+1] == dfa.transition(dfa_path[i], word[i])
            {
                NfaSequenceOfDfa2(dfa, word, nfa_path, dfa_path, i);
            }
            var fs := Pick(nfa_path[|word|]);
            assert |nfa_path[|word|]-{fs}| == 0;
            assert fs in dfa.acceptStates;
            assert dfa_path[|word|] == fs;
            assert dfa_path[|word|] in dfa.acceptStates;
            assert nfa_path[|word|] == {dfa_path[|word|]};
            assert dfa_path[|word|] in dfa.acceptStates;
        }
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

    ghost function ConcatenateLanguage<Alphabet>(l1: iset<seq<Alphabet>>, l2: iset<seq<Alphabet>>): iset<seq<Alphabet>>
    {
        iset x,y | x in l1 && y in l2 :: x + y
    }

    lemma RegularLanguageHasNFA<State(!new), Alphabet(!new)>(language: iset<seq<Alphabet>>, alphabet: set<Alphabet>)
        requires StateMachines.IsRegularLanguage<State, Alphabet>(language, alphabet)
        ensures exists nfa: NFA<State, Alphabet> :: ValidNfa(nfa) && NFALanguage(nfa) == language && nfa.alphabet == alphabet
    {
        var dfa: DFA<State, Alphabet> :| ValidDfa(dfa) && Language(dfa) == language && dfa.alphabet == alphabet;
        var nfa := DfaToNfa(dfa);
        DFA_NFA_Equivalent(dfa);
    }

    function ConcatNfas<State(!new), Alphabet(!new)>(nfa1: NFA<State, Alphabet>, nfa2: NFA<State, Alphabet>): NFA<State, Alphabet>
        requires ValidNfa(nfa1)
        requires ValidNfa(nfa2)
        requires nfa1.states !! nfa2.states
        requires nfa1.alphabet == nfa2.alphabet
        ensures ValidNfa(ConcatNfas(nfa1,nfa2))
    {
        var transitions: map<(State, Alphabet), set<State>> := nfa1.transitions + nfa2.transitions;
        var epsilonTransitions: map<State, set<State>> := nfa2.epsilonTransitions + map q | q in nfa1.epsilonTransitions.Keys + nfa1.acceptStates :: if q in nfa1.epsilonTransitions && q !in nfa1.acceptStates then
                // Case 1: q has epsilons but is NOT an accept state.
                // Action: Keep its original transitions only.
                nfa1.epsilonTransitions[q]
            else if q in nfa1.epsilonTransitions && q in nfa1.acceptStates then
                // Case 2: q has epsilons AND IS an accept state.
                // Action: Add the bridge to its existing transitions.
                nfa1.epsilonTransitions[q] + {nfa2.startState}
            else // This implies `q !in nfa1.epsilon_transitions` but `q in nfa1.acceptStates`
                // Case 3: q has no epsilons but IS an accept state.
                // Action: Create a new bridge transition.
                {nfa2.startState};
        NFA(nfa1.states + nfa2.states, nfa1.startState, nfa2.acceptStates, nfa1.alphabet, transitions, epsilonTransitions)
    }



    lemma {:isolate_assertions} ConcatNfasMatchLanguage<State(!new),Alphabet(!new)>(nfa1: NFA<State, Alphabet>, nfa2: NFA<State, Alphabet>)
        requires ValidNfa(nfa1)
        requires ValidNfa(nfa2)
        requires nfa1.states !! nfa2.states
        requires nfa1.alphabet == nfa2.alphabet
        ensures NFALanguage(ConcatNfas(nfa1, nfa2)) == ConcatenateLanguage(NFALanguage(nfa1), NFALanguage(nfa2))
    {
        var cnfa := ConcatNfas(nfa1, nfa2);
        forall word | word in NFALanguage(cnfa)
            ensures word in ConcatenateLanguage(NFALanguage(nfa1), NFALanguage(nfa2))
        {
            NfaExtendedDeltaComputesTrace(cnfa, word);
            NfaExtendedDeltaAccepting(cnfa, word);
            var cnfa_path :| IsValidNfaTrace(cnfa, word, cnfa_path) &&
                            NfaExtendedDelta(cnfa, {cnfa.startState}, word) == cnfa_path[|word|];
        }

        forall word | word in ConcatenateLanguage(NFALanguage(nfa1), NFALanguage(nfa2))
            ensures  word in NFALanguage(ConcatNfas(nfa1, nfa2))
        {
            var s1, s2 :| s1 + s2 == word && s1 in NFALanguage(nfa1) && s2 in NFALanguage(nfa2);
            assert NFAutomata.ValidString(nfa1, s1) && NFAutomata.Accepted(nfa1, s1);
            assert NFAutomata.ValidString(nfa2, s2) && NFAutomata.Accepted(nfa2, s2);

            NfaExtendedDeltaComputesTrace(nfa1, s1);
            NfaExtendedDeltaAccepting(nfa1, s1);
            var nfa_path1 :| IsValidNfaTrace(nfa1, s1, nfa_path1) &&
                            NfaExtendedDelta(nfa1, {nfa1.startState}, s1) == nfa_path1[|s1|];

            NfaExtendedDeltaComputesTrace(nfa2, s2);
            NfaExtendedDeltaAccepting(nfa2, s2);
            var nfa_path2 :| IsValidNfaTrace(nfa2, s2, nfa_path2) &&
                            NfaExtendedDelta(nfa2, {nfa2.startState}, s2) == nfa_path2[|s2|];
            assert IsValidNfaTrace(ConcatNfas(nfa1, nfa2), s1, nfa_path1);
            // assert IsValidNfaTrace(ConcatNfas(nfa1, nfa2), s2, nfa_path2);
        }
    }

    
    lemma ConcatenateOfRegularLanguagesIsRegular<State(!new),Alphabet(!new)>(
        L1: iset<seq<Alphabet>>, 
        L2: iset<seq<Alphabet>>, 
        alphabet: set<Alphabet>)
        requires IsRegularLanguage<State, Alphabet>(L1, alphabet)
        requires IsRegularLanguage<State, Alphabet>(L2, alphabet)
        ensures IsRegularLanguage<set<State>, Alphabet>(ConcatenateLanguage(L1, L2), alphabet)

    {
        var dfa1: DFA<State, Alphabet> :| ValidDfa(dfa1) && dfa1.alphabet == alphabet && L1 == Language(dfa1);
        var dfa2: DFA<State, Alphabet> :| ValidDfa(dfa2) && dfa2.alphabet == alphabet && L2 == Language(dfa2);
        var nfa1 := DfaToNfa(dfa1);
        var nfa2 := DfaToNfa(dfa2);
        DFA_NFA_Equivalent(dfa1);
        DFA_NFA_Equivalent(dfa2);
        assume nfa1.states !! nfa2.states;
        var cnfa := ConcatNfas(nfa1, nfa2);
        // ConcatNfaValid(nfa1, nfa2);
        ConcatNfasMatchLanguage(nfa1, nfa2);
        var dfa := NfaToDfa(cnfa);
        NFA_DFA_Equivalent(cnfa);
    }

}