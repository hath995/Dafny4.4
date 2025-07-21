module NFAutomata {
  export reveals *
  datatype NFA<!State(==), !Alphabet(==)> = NFA(
    states: set<State>,
    start_state: State,
    accept_states: set<State>,
    alphabet: set<Alphabet>,
    transitions: map<(State, Alphabet), set<State>>,
    epsilon_transitions: map<State, set<State>>
  )

  predicate ValidNFA<State, Alphabet>(nfa: NFA<State, Alphabet>)
  {
    nfa.start_state in nfa.states &&
    nfa.accept_states <= nfa.states &&
    (forall s, a :: s in nfa.states && a in nfa.alphabet ==> (s,a) in nfa.transitions && nfa.transitions[(s, a)] <= nfa.states) &&
    (forall s :: s in nfa.states && s in nfa.epsilon_transitions ==> nfa.epsilon_transitions[s] <= nfa.states)
  }


  function Delta<State, Alphabet>(nfa: NFA<State, Alphabet>, state_set: set<State>, symbol: Alphabet): set<State>
    requires ValidNFA(nfa)
    requires state_set <= nfa.states
  {
    set q, r | 
      q in state_set && 
      (q, symbol) in nfa.transitions && 
      r in nfa.transitions[(q, symbol)] 
      :: r
  }

  lemma DeltaResultIsSubsetOfStates<State, Alphabet>(nfa: NFA<State, Alphabet>, state_set: set<State>, symbol: Alphabet)
    requires ValidNFA(nfa)
    requires state_set <= nfa.states
    requires symbol in nfa.alphabet
    ensures Delta(nfa, state_set, symbol) <= nfa.states
  {
    // The body is empty because Dafny can now prove this directly.
  }

  // This is the extended transition function ("delta-hat") that processes a whole string.
  function DeltaHat<State, Alphabet>(nfa: NFA<State, Alphabet>, current_states: set<State>, input: seq<Alphabet>): set<State>
    requires ValidNFA(nfa)
    requires current_states <= nfa.states
    requires forall i | 0 <= i < |input| :: input[i] in nfa.alphabet // All input symbols are valid
    ensures DeltaHat(nfa, current_states, input) <= nfa.states
    decreases |input| // Termination is based on consuming the input string.
  {
    if |input| == 0 then
      // Base case: End of string. The final states are just the current states.
      current_states
    else 
      // Recursive step:
      // 1. Take the next symbol.
      var symbol := input[0];
      var rest_of_input := input[1..];

      // 2. Find all states reachable by consuming the symbol.
      var next_states := Delta(nfa, current_states, symbol);

      // 3. From this new set of states, find its full epsilon closure.
      var next_states_with_closure := EpsilonClosure(nfa, next_states);

      // 4. Recurse on the rest of the string from this new set of active states.
      DeltaHat(nfa, next_states_with_closure, rest_of_input)
    
  }

  function EpsilonClosure<State, Alphabet>(nfa: NFA<State, Alphabet>, current_set: set<State>): set<State>
    requires ValidNFA(nfa)
    requires current_set <= nfa.states // We must start with a valid set of states.
    ensures current_set <= EpsilonClosure(nfa, current_set)      // The closure must contain the original set.
    ensures EpsilonClosure(nfa, current_set) <= nfa.states       // The closure cannot contain states outside the NFA.
    decreases nfa.states - current_set // Termination metric: the set of states yet to be added.
                                      // This set strictly shrinks with each recursive call.
  {
    // Find all states reachable in one epsilon-step from the current_set.
    var one_step_away := set s, next | 
      s in current_set &&
      s in nfa.epsilon_transitions &&
      next in nfa.epsilon_transitions[s]
      :: next;


    // The new potential closure includes the original set plus the newly found states.
    var expanded_set := current_set + one_step_away;

    if expanded_set == current_set then
      // Fixed-point reached: no new states were added. We are done.
      current_set
    else
      // Recursive step: we found new states. Recurse with the larger set.
      // The termination metric nfa.states - expanded_set is smaller than
      // nfa.states - current_set, so Dafny knows this will terminate.
      EpsilonClosure(nfa, expanded_set)
  }

  lemma EpsilonClosureWithNoEpsilons<State, Alphabet>(nfa: NFA<State, Alphabet>,  current_set: set<State>)
    requires ValidNFA(nfa)
    requires current_set <= nfa.states // We must start with a valid set of states.
    requires nfa.epsilon_transitions == map[]
    ensures EpsilonClosure(nfa, current_set) == current_set
  {
  }

  predicate ValidString<State, Alphabet>(nfa: NFA<State, Alphabet>, input: seq<Alphabet>) {
    forall x :: x in input ==> x in nfa.alphabet
  }

  ghost predicate AcceptedWrong<State(!new,==), Alphabet(==)>(nfa: NFA<State, Alphabet>, input: seq<Alphabet>)
    requires ValidNFA(nfa)
    requires ValidString(nfa, input)
  {
    exists states: seq<State> :: |states| == |input|+1 && states[0] == nfa.start_state && states[|input|] in nfa.accept_states && (forall i :: 0 <= i < |states| ==> states[i] in nfa.states) && (forall i :: 1 < i < |states| ==> states[i] in nfa.transitions[(states[i-1],input[i-1])])
  }

  predicate Accepts<State, Alphabet>(nfa: NFA<State, Alphabet>, input: seq<Alphabet>)
    requires ValidNFA(nfa)
    requires ValidString(nfa, input)
  {
    // 1. The initial set of active states is the epsilon closure of the start state.
    var initial_states := EpsilonClosure(nfa, {nfa.start_state});
    
    // 2. Run the machine on the whole input string.
    var final_states := DeltaHat(nfa, initial_states, input);
    
    // 3. Check if any final state is an accept state.
    final_states * nfa.accept_states != {}
  }

  // A helper that defines what it means to go from a set of states S1 to a set of states S2
  // by processing one character `a`.
  predicate NfaTransitionStep<State, Alphabet>(nfa: NFA<State, Alphabet>, S1: set<State>, a: Alphabet, S2: set<State>)
      requires ValidNFA(nfa)
      requires S1 <= nfa.states
      requires a in nfa.alphabet
      ensures NfaTransitionStep(nfa, S1, a, S2) ==> S2 <= nfa.states
  {
      S2 == EpsilonClosure(nfa, Delta(nfa, S1, a))
  }

  // A predicate that checks if a sequence of *sets of states* is a valid trace
  // for the subset construction simulation of an NFA.
  predicate IsValidNfaTrace<State, Alphabet>(nfa: NFA<State, Alphabet>, w: seq<Alphabet>, trace: seq<set<State>>)
      requires ValidNFA(nfa)
      requires ValidString(nfa, w)
  {
      |trace| == |w| + 1 &&
      // The trace must start with the epsilon closure of the start state.
      trace[0] == EpsilonClosure(nfa, {nfa.start_state}) &&
      // Each subsequent set in the trace must be the result of a transition from the previous set.
      forall i :: 0 <= i < |w| ==> trace[i] <= nfa.states && NfaTransitionStep(nfa, trace[i], w[i], trace[i+1])
  }

  lemma UniqueNfaTrace<State, Alphabet>(nfa: NFA, w: seq<Alphabet>, trace1: seq<set<State>>, trace2: seq<set<State>>)
      requires ValidNFA(nfa) && ValidString(nfa, w)
      requires IsValidNfaTrace(nfa, w, trace1)
      requires IsValidNfaTrace(nfa, w, trace2)
      ensures trace1 == trace2
  {
      assert |trace1| == |trace2|;
      // Prove that the sequences are equal up to their full length.
      UniqueNfaTrace_PrefixesEqual(nfa, w, trace1, trace2, |trace1|);
      // This helper lemma proves trace1[..k] == trace2[..k]. For k=|trace1|, this means trace1==trace2.
  }

  // Proves that the prefixes of length `k` of two valid traces are identical.
  lemma UniqueNfaTrace_PrefixesEqual<State, Alphabet>(nfa: NFA, w: seq<Alphabet>, trace1: seq<set<State>>, trace2: seq<set<State>>, k: nat)
      requires ValidNFA(nfa) && ValidString(nfa, w)
      requires IsValidNfaTrace(nfa, w, trace1)
      requires IsValidNfaTrace(nfa, w, trace2)
      requires |trace1| == |trace2|
      requires k <= |trace1|
      ensures trace1[..k] == trace2[..k]
      decreases k
  {
      if k == 0 {
          // Base case: empty prefixes are equal.
      } else {
          // Inductive step: Assume prefixes of length k-1 are equal.
          UniqueNfaTrace_PrefixesEqual(nfa, w, trace1, trace2, k - 1);
          // IH: trace1[..k-1] == trace2[..k-1]
          
          // We need to prove trace1[k-1] == trace2[k-1].
          var i := k - 1; // The index we are interested in.
          
          if i == 0 {
              // If we are proving for index 0, it's the base case of the trace.
              assert trace1[0] == EpsilonClosure(nfa, {nfa.start_state});
              assert trace2[0] == EpsilonClosure(nfa, {nfa.start_state});
              assert trace1[0] == trace2[0];
          } else {
              // We need to look at the previous element, i-1.
              // Since `i-1 < k-1`, our IH `trace1[..k-1] == trace2[..k-1]` tells us that
              // all elements up to index k-2 are equal. This includes `i-1`.
              assert trace1[i-1] == trace2[i-1];
              
              // Now we use the definition of IsValidNfaTrace to compute trace[i].
              // It says trace[i] is computed from trace[i-1] and w[i-1].
              var prev_state1 := trace1[i-1];
              var prev_state2 := trace2[i-1];
              assert prev_state1 == prev_state2;

              var next_state1 := EpsilonClosure(nfa, Delta(nfa, prev_state1, w[i-1]));
              var next_state2 := EpsilonClosure(nfa, Delta(nfa, prev_state2, w[i-1]));

              assert trace1[i] == next_state1;
              assert trace2[i] == next_state2;
              assert next_state1 == next_state2;
              assert trace1[i] == trace2[i];
          }
          
          // We know from IH: trace1[..k-1] == trace2[..k-1]
          // We just proved: trace1[k-1] == trace2[k-1]
          // Together, this means trace1[..k] == trace2[..k].
      }
  }

  ghost predicate Accepted<State(!new), Alphabet(!new)>(nfa: NFA<State, Alphabet>, w: seq<Alphabet>)
      requires ValidNFA(nfa) && ValidString(nfa, w)
  {
      exists trace: seq<set<State>> :: 
          IsValidNfaTrace(nfa, w, trace) &&
          trace[|w|] * nfa.accept_states != {}
  }
  ghost function NFALanguage<State(!new), Alphabet(!new)>(nfa: NFA): iset<seq<Alphabet>> 
    requires ValidNFA(nfa)
  {
    iset w: seq<Alphabet> | ValidString(nfa, w) && Accepted(nfa, w)
  }
    
  // // Example usage and test cases
  method TestNFA() {
    // Create an NFA that accepts strings with an even number of 'a's
    var states := {0, 1};
    var start := 0;
    var accepts := {0};
    var alphabet := {'a', 'b'};
    var transitions := map[
      (0, 'a') := {1},
      (0, 'b') := {0},
      (1, 'a') := {0},
      (1, 'b') := {1}
    ];
    var eps_transitions := map[];
    
    var nfa: NFA<int,char> := NFA(states, start, accepts, alphabet, transitions, eps_transitions);
    
    // Test some strings
    // assert Accepts(nfa, ""); // 0 a's (even)
    // assert Accepts(nfa, "aa"); // 2 a's (even)
    assert !Accepts(nfa, "bab"); // 1 'a' (odd) - should not accept
    // assert Accepts(nfa, "baab"); // 2 a's (even)
  }
  

}