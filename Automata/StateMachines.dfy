module StateMachines {
  export reveals *

    datatype DFA<!State(==), !Alphabet(==)> = DFA(
        states: set<State>,
        alphabet: set<Alphabet>,
        transition: (State, Alphabet) -> State,
        startState: State,
        acceptStates: set<State>
    )

    predicate ValidTransitionFunction<State(==), Alphabet(==)>(d: DFA<State, Alphabet>)
    {
        forall s, a :: s in d.states && a in d.alphabet ==> d.transition(s, a) in d.states
    }

    predicate ValidDfa<State(==), Alphabet(==)>(d: DFA<State, Alphabet>)
    
    {
        d.startState in d.states &&
        d.acceptStates <= d.states &&
        ValidTransitionFunction(d)
    }

    datatype RegExp<Alphabet(==)> = 
  | Empty                           // ∅ - empty language
  | Epsilon                         // ε - empty string
  | Symbol(c: Alphabet)                 // single character
  | Union(left: RegExp, right: RegExp)      // r1 ∪ r2
  | Concat(left: RegExp, right: RegExp)     // r1 · r2
  | Star(r: RegExp)                 // r*

// Define what it means for a string to match a regular expression
predicate Matches<Alphabet(==)>(r: RegExp<Alphabet>, s: seq<Alphabet>)
  decreases r, |s|
{
  match r
  case Empty => false
  case Epsilon => |s| == 0
  case Symbol(c) => |s| == 1 && s[0] == c
  case Union(r1, r2) => Matches(r1, s) || Matches(r2, s)
  case Concat(r1, r2) => 
    (exists k :: 0 <= k <= |s| && Matches(r1, s[..k]) && Matches(r2, s[k..]))
  case Star(r') => 
    s == [] || 
    // (exists k :: 1 <= k <= |s| && Matches(r', s[..k]) && Matches(Star(r'), s[k..]))
    (exists k :: 1 <= k < |s| && Matches(r', s[..k]) && Matches(Star(r'), s[k..])) ||
    (Matches(r', s))
}

ghost function V<Alphabet(!new,==)>(base: iset<seq<Alphabet>>, n: nat): iset<seq<Alphabet>> {
    if n == 0 then iset{[]} 
    else if n == 1 then base else
    iset w,v | w in V(base, n-1) && v in base :: v+w
}

ghost function Kleene<Alphabet(!new,==)>(base: iset<seq<Alphabet>>): iset<seq<Alphabet>>
{
    iset x, n | x in V(base, n) :: x
}

lemma EmptyStringIsInKleene<Alphabet(!new,==)>(base: iset<seq<Alphabet>>)
    ensures [] in Kleene(base)
{
    // Goal: To show `[] in Kleene(base)`, we must find a witness `n`
    // such that `[] in V(base, n)`.

    // Let's choose our witness n = 0.
    var n: nat := 0;

    // By definition of V, V(base, 0) is iset{[]}.
    var V_n0 := V(base, 0);
    assert V_n0 == iset{[]};

    // Therefore, the empty string `[]` is an element of V(base, 0).
    assert [] in V_n0;

    // Since `[]` is in `V(base, n)` for our chosen `n`, it must be
    // in the larger set `Kleene(base)` by definition of Kleene.
    // The existential `exists n :: [] in V(base, n)` is satisfied.
    assert [] in Kleene(base);
}

lemma BaseIsSubsetOfKleene<Alphabet(!new,==)>(base: iset<seq<Alphabet>>)
    ensures base <= Kleene(base)
{
    // To prove a subset relation `A <= B`, we must show that for any
    // arbitrary element `s` in `A`, it is also in `B`.
    forall s | s in base
        ensures s in Kleene(base)
    {
        // Goal: To show `s in Kleene(base)`, we must find a witness `n`
        // such that `s in V(base, n)`.

        // Let's choose our witness n = 1.
        var n: nat := 1;

        // By definition of V, V(base, 1) is simply `base`.
        var V_n1 := V(base, 1);
        assert V_n1 == base;

        // Since we are assuming `s in base`, and `V(base, 1) == base`,
        // it must be that `s` is in `V(base, 1)`.
        assert s in V_n1;

        // Since `s` is in `V(base, n)` for our chosen `n`, it must be
        // in the larger set `Kleene(base)` by definition of Kleene.
        assert s in Kleene(base);
    }
}

lemma V_concat_lemma<Alphabet(!new,==)>(base: iset<seq<Alphabet>>, w: seq<Alphabet>, v: seq<Alphabet>, n: nat, m: nat)
    requires w in V(base, n)
    requires v in V(base, m)
    ensures w+v in V(base, n+m)
    decreases n // We induct on n, the size of the first string `w`.
{
    if n == 0 {
        // Base Case: w is built from 0 elements.
        // `requires w in V(base, 0)` implies w must be the empty string.
        assert w == [];
        
        // Our goal is `w+v in V(base, 0+m)`, which is `[]+v in V(base, m)`.
        // This simplifies to `v in V(base, m)`, which is true by the lemma's `requires` clause.
        assert w+v == v;
        assert w+v in V(base, m);
    } 
    else { // n > 0, the Inductive Step
        // Since `w in V(base, n)` and n > 0, we can decompose `w` according
        // to the new definition of V.
        var w_prefix, w_suffix :| w == w_prefix + w_suffix && w_prefix in base && w_suffix in V(base, n-1);

        // Our goal is to prove `w+v in V(base, n+m)`.
        // Let's substitute our decomposition of `w`:
        // (w_prefix + w_suffix) + v in V(base, n+m)
        
        // By the associativity of string concatenation, this is equal to:
        // w_prefix + (w_suffix + v)
        assert w+v == w_prefix + (w_suffix + v);

        // Now, let's analyze the inner part: `w_suffix + v`.
        // We have `w_suffix in V(base, n-1)` and `v in V(base, m)`.
        // This is exactly the premise of our lemma, but for a smaller `n`.
        // We can make a recursive call (this is the induction hypothesis).
        V_concat_lemma(base, w_suffix, v, n-1, m);
        
        // The `ensures` clause of the recursive call gives us a crucial fact:
        var new_suffix := w_suffix + v;
        assert new_suffix in V(base, (n-1)+m);
        assert new_suffix in V(base, n+m-1);

        // Our goal has now become: `w_prefix + new_suffix in V(base, n+m)`.
        // Let's look at the definition of `V(base, n+m)`.
        // Since n > 0, n+m >= 1. The definition is `iset v',w' | v' in base && w' in V(base, n+m-1) :: v'+w'`.
        
        // This is a perfect match! We have witnesses for this set comprehension:
        // 1. `v' := w_prefix`. We know `w_prefix in base`.
        // 2. `w' := new_suffix`. We just proved `new_suffix in V(base, n+m-1)`.
        
        // Since our witnesses satisfy the conditions, their concatenation must be in the set.
        assert w_prefix + new_suffix in V(base, n+m);
        
        // Therefore, our original goal is proven.
        assert w+v in V(base, n+m);
    }
}



lemma MatchesImpliesLanguage<Alphabet(!new,==)>(r: RegExp<Alphabet>, s: seq<Alphabet>)
    requires r.Star?
    // This is the essential Induction Hypothesis from the (unstated) outer structural induction.
    requires forall s' :: Matches(r.r, s') <==> s' in RegexLanguage(r.r)
    
    // Original requirements
    requires Matches(r, s)
    ensures s in RegexLanguage(r)
    decreases |s|, r
{
    var r_prime := r.r;
    var baseLang := RegexLanguage(r_prime);

    // Goal: Show `s in Kleene(baseLang)`. This means finding an `n` where `s in V(baseLang, n)`.

    // We proceed by cases on why `Matches(Star(r_prime), s)` is true.
    if s == [] {
        // Case 1: The empty string.
        // We need to find an n where [] in V(baseLang, n). We choose n=0.
        assert [] in V(baseLang, 0);
        // Therefore, [] is in the Kleene set.
        assert [] in Kleene(baseLang);
    }
    else if Matches(r_prime, s) {
        // Case 2: `s` itself is one string from the base language.
        // We need an n where s in V(baseLang, n). We choose n=1.
        // V(baseLang, 1) is just `baseLang`.
        // By the Induction Hypothesis (from requires), `Matches(r_prime, s)` implies `s in baseLang`.
        // RegexMatchLanguageLemma(r_prime);
        assert s in baseLang;
        assert s in V(baseLang, 1);
        assert s in Kleene(baseLang);
    }
    else // Case 3: The recursive existential `exists k...` holds.
    {
        var k :| 1 <= k < |s| && Matches(r_prime, s[..k]) && Matches(Star(r_prime), s[k..]);
        var p := s[..k];
        var suffix := s[k..];

        // Part A: Analyze the prefix `p`.
        // We know `Matches(r_prime, p)`. By the IH, this means `p in baseLang`.
        // RegexMatchLanguageLemma(r_prime);
        assert p in baseLang;
        // This is equivalent to `p in V(baseLang, 1)`.
        
        // Part B: Analyze the `suffix`.
        // We know `Matches(Star(r_prime), suffix)`. This is our lemma on a shorter string.
        // We can make a recursive call.
        MatchesImpliesLanguage(r, suffix);
        // The recursive call ensures `suffix in RegexLanguage(r)`, which is `suffix in Kleene(baseLang)`.
        assert suffix in Kleene(baseLang);

        // By definition of `Kleene`, this means there exists some `m` for the suffix.
        var m:nat :| suffix in V(baseLang, m);

        // Part C: Combine them.
        // We have `p in V(baseLang, 1)` and `suffix in V(baseLang, m)`.
        // Now we use our powerful helper lemma!
        V_concat_lemma(baseLang, p, suffix, 1, m);
        
        // The helper ensures `p+suffix` is in `V(baseLang, 1+m)`.
        assert p+suffix in V(baseLang, 1+m);
        assert s == p + suffix;
        // Since s = p+suffix, s is in `V` for n = 1+m.
        assert s in V(baseLang, 1+m);
        // Therefore, s is in the Kleene set.
        assert s in Kleene(baseLang);
    }

    // In all cases, the `ensures` clause holds.
}
lemma ConcatMatchesStar<Alphabet(!new,==)>(r_prime: RegExp<Alphabet>, p: seq<Alphabet>, suffix: seq<Alphabet>)
    // If p matches r' and suffix matches Star(r'), then p+suffix matches Star(r').
    requires Matches(r_prime, p)
    requires Matches(Star(r_prime), suffix)
    ensures Matches(Star(r_prime), p+suffix)
    decreases |suffix| // The induction is now on the length of the Star-matching part.
{
    // Our goal is to prove `Matches(Star(r_prime), p+suffix)`.
    // Let s := p+suffix.
    // We use the definition: `s==[] || (exists k...) || Matches(r_prime, s)`

    // Since `Matches(r_prime, p)` is true, `p` cannot be empty unless the language of r_prime contains ε.
    // In any case, `p+suffix` is likely not empty.
    // Let's satisfy the `exists k...` clause.

    // Let our witness be k := |p|.
    // Since Matches(r_prime, p) is true, if p is not empty, then |p| >= 1.
    // If p is empty, this choice of k=0 doesn't work for the 1<=k requirement.
    
    if |p| == 0 {
        // If p is empty, then p+suffix == suffix.
        // The goal becomes `Matches(Star(r_prime), suffix)`, which is true by the `requires` clause.
        assert p+suffix == suffix;
        assert Matches(Star(r_prime), p+suffix);
    } else {
        // Since p is not empty, |p| >= 1. Let k := |p|.
        // We need to check the parts of the existential for `s = p+suffix`.
        
        // 1. `1 <= k < |s|` or `k = |s|`?
        //    `k = |p|`, so `k >= 1`.
        
        // 2. Check `Matches(r_prime, s[..k])`.
        //    `s[..k]` is `(p+suffix)[..|p|]`, which is `p`.
        //    The condition is `Matches(r_prime, p)`, which is true by the `requires` clause.
        
        // 3. Check `Matches(Star(r_prime), s[k..])`.
        //    `s[k..]` is `(p+suffix)[|p|..]`, which is `suffix`.
        //    The condition is `Matches(Star(r_prime), suffix)`, which is true by the `requires` clause.

        // We have a `k` (|p|) that satisfies the original `exists k: 1 <= k <= |s|` definition.
        // Let's see if it works for your symmetric one.
        if |suffix| == 0 {
            // Then k = |p| = |s|.
            // This means we need to satisfy the `Matches(r_prime, s)` clause.
            // Our s is `p`. We know `Matches(r_prime, p)`. This works.
            assert p+suffix == p;
            assert Matches(Star(r_prime), p+suffix);
        } else {
            // Then k = |p| < |p|+|suffix| = |s|.
            // This satisfies the `exists k: 1 <= k < |s|` clause.
            var s := p+suffix;
            assert 1 <= |p| < |s|;
            assert Matches(r_prime, s[..|p|]);
            assert Matches(Star(r_prime), s[|p|..]);
            assert Matches(Star(r_prime), p+suffix);
        }
    }
}

lemma LanguageImpliesMatches_V_Helper<Alphabet(!new,==)>(r_prime: RegExp<Alphabet>, s: seq<Alphabet>, n: nat)
    requires forall s' :: s' in RegexLanguage(r_prime) <==> Matches(r_prime, s')
    requires s in V(RegexLanguage(r_prime), n)
    ensures Matches(Star(r_prime), s)
    decreases n
{
    var baseLang := RegexLanguage(r_prime);
    
    if n == 0 {
        // Base case: s is in V(base, 0), so s must be [].
        assert s == [];
        // The first clause of Matches(Star...) is `s == []`, so the goal holds.
        assert Matches(Star(r_prime), s);
    } else { // n > 0, the inductive step
        // By our new definition of V, s can be written as v + w,
        // where v is from the base and w is built from n-1 pieces.
        var v, w :| s == v + w && v in baseLang && w in V(baseLang, n-1);

        // Part 1: Analyze the prefix `v`.
        // We know `v in baseLang`, which is `RegexLanguage(r_prime)`.
        // By the outer IH (from the `requires` clause), this implies `Matches(r_prime, v)`.
        assert Matches(r_prime, v);
        // Since `v` must be concatenated with `w` (which is in V(n-1) and thus non-empty if n-1>0,
        // or empty if n-1=0), we know `v` cannot be the whole string `s` unless `w` is empty.
        // We also know `|v| > 0` if `baseLang` doesn't contain `[]`. Let's assume non-empty strings for now.

        // Part 2: Analyze the suffix `w`.
        // We know `w in V(baseLang, n-1)`. We can use our induction hypothesis on the smaller `n-1`.
        LanguageImpliesMatches_V_Helper(r_prime, w, n-1);
        // This ensures that `w` matches the Star expression.
        assert Matches(Star(r_prime), w);

        // Part 3: Combine them. Our goal is to prove `Matches(Star(r_prime), s)`.
        // Let's use the `exists k...` clause of the `Matches(Star...)` definition.
        // Our candidate for `k` is `|v|`. Let's check the conditions for `s = v+w`:
        
        // 1. `1 <= k < |s|` or `k = |s|`?
        //    If `v` is not empty, `k=|v| >= 1`. If `w` is not empty, `k < |s|`.
        //    If `w` is empty, `k=|s|`.
        
        // 2. `Matches(r_prime, s[..k])`?
        //    `s[..k]` is `(v+w)[..|v|]`, which is `v`.
        //    The condition is `Matches(r_prime, v)`, which we proved in Part 1.
        
        // 3. `Matches(Star(r_prime), s[k..])`?
        //    `s[k..]` is `(v+w)[|v|..]`, which is `w`.
        //    The condition is `Matches(Star(r_prime), w)`, which we proved in Part 2.
        
        // The existential is satisfied. The proof is complete without needing any complex helper lemmas.
        if v == [] {
            assert v+w == w;
        }else if w == [] {
            assert v+w == v;
        }else{
            assert 1 <= |v| < |s|;
            assert Matches(r_prime, s[..|v|]);

        }
        
        assert Matches(Star(r_prime), s);
    }
}
lemma LanguageImpliesMatches<Alphabet(!new,==)>(r: RegExp<Alphabet>, s: seq<Alphabet>)
    requires r.Star?
    // This is the IH that gets passed to the helper.
    requires forall s' :: s' in RegexLanguage(r.r) <==> Matches(r.r, s')
    
    // The premise for this specific lemma.
    requires s in RegexLanguage(r)
    ensures Matches(r, s)
{
    var r_prime := r.r;
    var baseLang := RegexLanguage(r_prime);
    
    // The premise `s in RegexLanguage(r)` means `s in Kleene(baseLang)`.
    // By definition of Kleene, there must exist an `n` such that `s in V(baseLang, n)`.
    var n: nat :| s in V(baseLang, n);

    // Now, call our powerful helper lemma with the witness `n`.
    LanguageImpliesMatches_V_Helper(r_prime, s, n);

    // The ensures clause of the helper directly proves our goal.
}

ghost function RegexLanguage<Alphabet(!new,==)>(r: RegExp<Alphabet>) : iset<seq<Alphabet>>
{
    match r
    case Empty => iset{}
    case Epsilon => iset{[]}
    case Symbol(c) => iset{[c]}
    case Union(r1, r2) => iset s | s in RegexLanguage(r1) || s in RegexLanguage(r2) :: s
    case Concat(r1, r2) => iset s1, s2 | s1 in RegexLanguage(r1) && s2 in RegexLanguage(r2) :: s1 + s2
    case Star(r) => Kleene(RegexLanguage(r))
}


ghost function RegexMatchLanguage<Alphabet(!new,==)>(r: RegExp<Alphabet>) : iset<seq<Alphabet>>
{
    iset s | Matches(r, s) :: s
}

lemma RegexMatchLanguageEpsilon<Alphabet(!new,==)>(r: RegExp<Alphabet>)
    requires r.Epsilon?
    ensures RegexMatchLanguage(r) == iset{[]}
{
    assert forall s | Matches(r, s) :: s == [];
    assert forall x :: x in iset{[]} ==> x in RegexMatchLanguage(r) by {
        forall x | x in iset{[]}
        ensures x in RegexMatchLanguage(r)
        {
            if x == [] {
                assert Matches(r, []);
                assert x in RegexMatchLanguage(r);
            } else {
                assert false;
            }
        }
    }
}

lemma RegexMatchLanguageSymbol<Alphabet(!new,==)>(r: RegExp<Alphabet>)
    requires r.Symbol?
    ensures RegexMatchLanguage(r) == iset{[r.c]}
{
    assert forall s | Matches(r, s) :: s == [r.c];
    assert forall x :: x in iset{[r.c]} ==> x in RegexMatchLanguage(r) by {
        forall x | x in iset{[r.c]}
            ensures x in RegexMatchLanguage(r)
        {
            if x == [r.c] {
                assert Matches(r, [r.c]);
                assert x in RegexMatchLanguage(r);
            } else {
                assert false;
            }
        }
    }
}

lemma RegexMatchLanguageUnion<Alphabet(!new,==)>(r1: RegExp<Alphabet>)
    requires r1.Union?
    ensures RegexMatchLanguage(r1.left) + RegexMatchLanguage(r1.right) == RegexMatchLanguage(r1)
{
    assert forall s | s in RegexMatchLanguage(r1) :: s in RegexMatchLanguage(r1.left) + RegexMatchLanguage(r1.right) by {
        forall s | s in RegexMatchLanguage(r1)
            ensures s in RegexMatchLanguage(r1.left) + RegexMatchLanguage(r1.right)
        {
            assert Matches(r1, s);
        }
    }
    assert forall x :: x in RegexMatchLanguage(r1.left) + RegexMatchLanguage(r1.right) ==> x in RegexMatchLanguage(r1) by {
        forall x | x in RegexMatchLanguage(r1.left) + RegexMatchLanguage(r1.right)
            ensures x in RegexMatchLanguage(r1)
        {
            if x in RegexMatchLanguage(r1.left) {
                assert Matches(r1.left, x);
                assert Matches(r1, x);
                assert x in RegexMatchLanguage(r1);
            } else if x in RegexMatchLanguage(r1.right) {
                assert Matches(r1.right, x); 
                assert Matches(r1, x);
                assert x in RegexMatchLanguage(r1);
            } else {
                assert false;
            }
        }
    }
}

lemma RegexMatchLanguageConcat<Alphabet(!new,==)>(r1: RegExp<Alphabet>)
    requires r1.Concat?
    ensures RegexMatchLanguage(r1) == iset s1, s2 | s1 in RegexMatchLanguage(r1.left) && s2 in RegexMatchLanguage(r1.right) :: s1 + s2
{
    forall s | s in (iset s1, s2 | s1 in RegexMatchLanguage(r1.left) && s2 in RegexMatchLanguage(r1.right) :: s1 + s2)
        ensures s in RegexMatchLanguage(r1)
    {
        var left, right :| s == left+right && left in RegexMatchLanguage(r1.left) && right in RegexMatchLanguage(r1.right);
        assert 0 <= |left| <= |s|;
        assert |left|+|right| == |s|;
        assert Matches(r1.left, s[..|left|]);
        assert Matches(r1.right, s[|left|..]);
        assert Matches(r1, s);
    }
    
    forall s | s in RegexMatchLanguage(r1)
        ensures s in iset s1, s2 | s1 in RegexMatchLanguage(r1.left) && s2 in RegexMatchLanguage(r1.right) :: s1 + s2 
    {
        var k :| 0 <= k <= |s| && Matches(r1.left, s[..k]) && Matches(r1.right, s[k..]);
        assert s[..k] in RegexMatchLanguage(r1.left);
        assert s[k..] in RegexMatchLanguage(r1.right);
        assert s == s[..k]+s[k..];
    }

}

lemma RegexMatchLanguageLemma<Alphabet(!new,==)>(r: RegExp<Alphabet>)
    ensures RegexMatchLanguage(r) == RegexLanguage(r)
    decreases r
{
    if r.Empty? {
        assert RegexMatchLanguage(r) == iset{};
        assert RegexLanguage(r) == iset{};
    } else if r.Epsilon? {
        RegexMatchLanguageEpsilon(r);
        assert RegexMatchLanguage(r) == iset{[]};
        assert RegexLanguage(r) == iset{[]};
    } else if r.Symbol? {
        RegexMatchLanguageSymbol(r);
        assert RegexMatchLanguage(r) == iset{[r.c]};
        assert RegexLanguage(r) == iset{[r.c]};
    } else if r.Union? {
        RegexMatchLanguageUnion(r);
        assert RegexMatchLanguage(r) == RegexMatchLanguage(r.left) + RegexMatchLanguage(r.right);
        assert RegexLanguage(r) == RegexLanguage(r.left) + RegexLanguage(r.right);
    } else if r.Concat? {
        RegexMatchLanguageConcat(r);
        assert RegexMatchLanguage(r) == iset s1, s2 | s1 in RegexMatchLanguage(r.left) && s2 in RegexMatchLanguage(r.right) :: s1 + s2;
        assert RegexLanguage(r) == iset s1, s2 | s1 in RegexLanguage(r.left) && s2 in RegexLanguage(r.right) :: s1 + s2;
    } else if r.Star? {
            var r_prime := r.r;
            // 1. Establish the Induction Hypothesis for the sub-expression.
            // This is the most important step.
            RegexMatchLanguageLemma(r_prime);
            // We now have the crucial fact for our helpers:
            // forall s' :: Matches(r_prime, s') <==> s' in RegexLanguage(r_prime)

            // 2. Prove the equivalence for Star using our helpers.
            // To prove the sets are equal, we show equivalence for any element `s`.
            forall s: seq<Alphabet>
                ensures Matches(Star(r_prime), s) <==> s in RegexLanguage(Star(r_prime))
            {
                // Direction 1: Matches ==> Language
                if Matches(Star(r_prime), s) {
                    // Call the helper lemma for this direction.
                    // It is now provable because its `requires` clause (the IH) is met.
                    MatchesImpliesLanguage(r, s);
                    assert s in RegexLanguage(r);
                }

                // Direction 2: Language ==> Matches
                if s in RegexLanguage(r) {
                    // Call the helper lemma for this direction.
                    LanguageImpliesMatches(r, s);
                    assert Matches(r, s);
                }
            }
            // Since we've shown forall s :: s in A <==> s in B, we can conclude A == B.
            assert RegexMatchLanguage(r) == RegexLanguage(r);
    }
}


    lemma StateSequenceInDFA<State(!new,==), Alphabet(==)>(d: DFA<State, Alphabet>, s: seq<Alphabet>, states: seq<State>)
        requires ValidDfa(d) && ValidString(d, s)
        requires |states| == |s| + 1
        requires states[0] in d.states
        requires forall i :: 1 <= i < |states| ==> states[i] == d.transition(states[i-1], s[i-1])
        ensures forall k :: k in states ==> k in d.states
    {
        // Build up proof from states[..1] to states[..|s|+1] step by step
        StateSequenceInDFABuildUp(d, s, states, |s|);
        // Now we have forall k :: k in states[..|s|+1] ==> k in d.states
        // assert states[..|s|+1] == states;
        // assert forall k :: k in states ==> k in d.states;
    }

    lemma StateSequenceInDFABuildUp<State(!new,==), Alphabet(==)>(d: DFA<State, Alphabet>, s: seq<Alphabet>, states: seq<State>, i: nat)
        requires ValidDfa(d) && ValidString(d, s)
        requires |states| == |s| + 1
        requires states[0] in d.states
        requires forall j :: 1 <= j < |states| ==> states[j] == d.transition(states[j-1], s[j-1])
        requires 0 <= i <= |s|
        ensures forall k :: k in states[..i+1] ==> k in d.states
        decreases i
    {
        if i == 0 {
            // Base case: establish that states[..0] has property (vacuously true)
            assert states[..0] == [];
            assert forall k :: k in states[..0] ==> k in d.states;
            // Now prove for states[..1]
            StateSequenceInDFAIterative(d, s, states, 0);
        } else {
            // Recursive case: establish states[..i] first, then prove states[..i+1]
            StateSequenceInDFABuildUp(d, s, states, i - 1);
            assert forall k :: k in states[..i] ==> k in d.states;
            StateSequenceInDFAIterative(d, s, states, i);
        }
    }

    lemma StateSequenceInDFAIterative<State(!new,==), Alphabet(==)>(d: DFA<State, Alphabet>, s: seq<Alphabet>, states: seq<State>, i: nat)
        requires ValidDfa(d) && ValidString(d, s)
        requires |states| == |s| + 1
        requires states[0] in d.states
        requires forall j :: 1 <= j < |states| ==> states[j] == d.transition(states[j-1], s[j-1])
        requires 0 <= i <= |s|
        requires forall k :: k in states[..i] ==> k in d.states
        ensures forall k :: k in states[..i+1] ==> k in d.states
    {
        if i == 0 {
            // Base case: prove states[..1] = [states[0]] has all elements in d.states
            assert states[..1] == [states[0]];
            assert states[0] in d.states; // given as precondition
            assert forall k :: k in states[..1] ==> k in d.states;
        } else {
            // Inductive step: assume states[..i] has all elements in d.states
            // prove states[..i+1] has all elements in d.states
            
            // Precondition establishes that states[..i] has all elements in d.states
            
            // Use sequence extensionality: states[..i+1] == states[..i] + [states[i]]
            assert states[..i+1] == states[..i] + [states[i]];
            
            // Prove states[i] in d.states
            // states[i] == d.transition(states[i-1], s[i-1])
            assert states[i] == d.transition(states[i-1], s[i-1]);
            assert states[i-1] in states[..i]; // since i-1 < i
            assert states[i-1] in d.states;   // from precondition
            assert s[i-1] in d.alphabet;      // from ValidString
            assert ValidTransitionFunction(d);
            assert d.transition(states[i-1], s[i-1]) in d.states;
            assert states[i] in d.states;
            
            // Now by sequence extensionality: states[..i+1] == states[..i] + [states[i]]
            // Since all elements in states[..i] are in d.states (precondition)
            // and states[i] is in d.states (just proven)
            // then all elements in states[..i+1] are in d.states
            forall k | k in states[..i+1]
                ensures k in d.states
            {
                if k in states[..i] {
                    assert k in d.states; // from precondition
                } else {
                    assert k == states[i]; // since states[..i+1] == states[..i] + [states[i]]
                    assert k in d.states;
                }
            }
        }
    }

    predicate ValidString<State(==), Alphabet(==)>(d: DFA<State, Alphabet>, s: seq<Alphabet>)
    {
        forall x :: x in s ==> x in d.alphabet
    }

    ghost predicate Accepted<State(!new,==), Alphabet(==)>(d: DFA<State, Alphabet>, s: seq<Alphabet>)
        requires ValidDfa(d) && ValidString(d, s)
    {
        exists states: seq<State> :: |states| == |s| + 1 && states[0] == d.startState &&
            states[|s|] in d.acceptStates &&
            (forall i :: 0 <= i < |states| ==> states[i] in d.states) &&
            (forall i :: 1 <= i < |s| + 1 ==> states[i] == d.transition(states[i-1], s[i-1]))
    }

    lemma AcceptedRequiresAcceptState<State(!new,==), Alphabet(==)>(d: DFA<State, Alphabet>, s: seq<Alphabet>, states: seq<State>)
        requires ValidDfa(d) && ValidString(d, s)
        requires |states| == |s| + 1
        requires states[0] == d.startState
        requires forall j :: j in states ==> j in d.states
        requires forall j :: 1 <= j < |states| ==> d.transition(states[j-1], s[j-1]) == states[j]
        ensures states[|s|] !in d.acceptStates ==> Accepted(d, s) == false
    {
        if states[|s|] !in d.acceptStates {
            // Prove by contradiction: assume Accepted(d, s) is true
            if Accepted(d, s) {
                // Then there exists some sequence of states that ends in an accept state
                var witnessStates :| |witnessStates| == |s| + 1 && 
                                    witnessStates[0] == d.startState && 
                                    witnessStates[|s|] in d.acceptStates && 
                                    (forall i :: 0 <= i < |witnessStates| ==> witnessStates[i] in d.states) && 
                                    (forall i :: 1 <= i < |s| + 1 ==> witnessStates[i] == d.transition(witnessStates[i-1], s[i-1]));
                
                // But since the DFA is deterministic, the sequence of states is unique
                // We'll prove that witnessStates == states
                UniqueStateSequence(d, s, states, witnessStates);
                
                // This leads to a contradiction: states[|s|] == witnessStates[|s|]
                // but states[|s|] !in d.acceptStates while witnessStates[|s|] in d.acceptStates
                assert false;
            }
        }
    }


    lemma UniqueStateSequence<State(!new,==), Alphabet(==)>(d: DFA<State, Alphabet>, s: seq<Alphabet>, states1: seq<State>, states2: seq<State>)
        requires ValidDfa(d) && ValidString(d, s)
        requires |states1| == |s| + 1 && |states2| == |s| + 1
        requires states1[0] == d.startState && states2[0] == d.startState
        requires forall j :: 0 <= j < |states1| ==> states1[j] in d.states
        requires forall j :: 0 <= j < |states2| ==> states2[j] in d.states
        requires forall j :: 1 <= j < |states1| ==> states1[j] == d.transition(states1[j-1], s[j-1])
        requires forall j :: 1 <= j < |states2| ==> states2[j] == d.transition(states2[j-1], s[j-1])
        ensures states1 == states2
    {
        // Prove by induction that states1[i] == states2[i] for all valid i
        assert states1 == states1[..|s|+1];
        assert states2 == states2[..|s|+1];
        assert states1[..0] == [];
        assert states2[..0] == [];
        assert states1[..0] == states2[..0];
        UniqueStateSequenceHelper(d, s, states1, states2, 0);
        // After the helper proves states1[..|s|+1] == states2[..|s|+1], 
        // we can conclude states1 == states2
        assert states1[..|s|+1] == states2[..|s|+1];
        assert states1 == states2;
    }

    lemma UniqueStateSequenceHelper<State(!new,==), Alphabet(==)>(d: DFA<State, Alphabet>, s: seq<Alphabet>, states1: seq<State>, states2: seq<State>, i: nat)
        requires ValidDfa(d) && ValidString(d, s)
        requires |states1| == |s| + 1 && |states2| == |s| + 1
        requires states1[0] == d.startState && states2[0] == d.startState
        requires forall j :: 0 <= j < |states1| ==> states1[j] in d.states
        requires forall j :: 0 <= j < |states2| ==> states2[j] in d.states
        requires forall j :: 1 <= j < |states1| ==> states1[j] == d.transition(states1[j-1], s[j-1])
        requires forall j :: 1 <= j < |states2| ==> states2[j] == d.transition(states2[j-1], s[j-1])
        requires i <= |s|
        requires states1[..i] == states2[..i]
        ensures states1 == states2
        decreases |s| - i
    {
        if i == |s| {
            // Base case: we've proven equality for all indices
            assert states1[..i+1] == states1[..|s|+1];
            assert states1[..i+1] == states2[..i+1];
            assert states1[..|s|+1] == states1;
            assert states2[..|s|+1] == states2;
            assert states1 == states2;
        } else {
            // Inductive step: prove states1[i] == states2[i]
            if i == 0 {
                // Base case: both start with startState
                assert states1[0] == d.startState == states2[0];
                assert states1[..1] == [states1[0]];
                assert states2[..1] == [states2[0]];
                assert states1[..1] == states2[..1];
            } else {
                // We know states1[..i] == states2[..i] by the precondition
                // This means states1[i-1] == states2[i-1]
                assert states1[i-1] == states2[i-1];
                // Both use the same transition function
                assert states1[i] == d.transition(states1[i-1], s[i-1]);
                // Therefore states1[i] == states2[i]
                assert states1[i] == states2[i];
                // So states1[..i+1] == states2[..i+1]
                assert states2[..i+1] == states2[..i] + [states2[i]];
                assert states1[..i+1] == states2[..i+1];
            }
            // Continue the induction
            UniqueStateSequenceHelper(d, s, states1, states2, i + 1);
        }
    }

    predicate Accepts<State(!new, ==), Alphabet(==)>(d: DFA<State, Alphabet>, s: seq<Alphabet>, states: seq<State>, i: nat)
        requires ValidDfa(d) && ValidString(d, s)
        requires 0 <= i <= |s|
        requires |states| == i + 1
        requires |states| > 0 && states[0] == d.startState
        requires forall j :: j in states ==> j in d.states
        requires forall j :: 1 <= j < |states| ==> d.transition(states[j-1], s[j-1]) == states[j]
        ensures Accepts(d, s, states, i) == Accepted(d, s)
        decreases |s| - i
    {
        if i == |s| then
            AcceptedRequiresAcceptState(d, s, states);
            states[i] in d.acceptStates
        else 
            Accepts(d, s, states + [d.transition(states[i], s[i])], i + 1)

    }

    predicate Accept2<State(!new,==), Alphabet(==)>(d: DFA<State, Alphabet>, s: seq<Alphabet>)
        requires ValidDfa(d) && ValidString(d, s)
        // ensures Accept2(d, s) == Accepted(d, s)
        decreases |s|
    {
        if |s| == 0 then
            // AcceptedRequiresAcceptState(d, s, [d.startState]);
            d.startState in d.acceptStates
        else
            Accept2(DFA(d.states, d.alphabet, d.transition, d.transition(d.startState, s[0]), d.acceptStates), s[1..])
    }

    lemma Accept2EqualsAccepted<State(!new,==), Alphabet(==)>(d: DFA<State, Alphabet>, s: seq<Alphabet>)
        requires ValidDfa(d) && ValidString(d, s)
        ensures Accept2(d, s) == Accepted(d, s)
    {
        Accept2ImpliesAccepted(d, s);
        AcceptedImpliesAccept2(d, s);
    }

    lemma Accept2ImpliesAccepted<State(!new,==), Alphabet(==)>(d: DFA<State, Alphabet>, s: seq<Alphabet>)
        requires ValidDfa(d) && ValidString(d, s)
        ensures Accept2(d, s) ==> Accepted(d, s)
        decreases |s|
    {
        if Accept2(d, s) {
            if |s| == 0 {
                // Base case: Accept2(d, []) == (d.startState in d.acceptStates)
                assert d.startState in d.acceptStates;
                var states := [d.startState];
                assert |states| == |s| + 1;
                assert states[0] == d.startState;
                assert states[|s|] in d.acceptStates;
                assert forall i :: 0 <= i < |states| ==> states[i] in d.states;
                assert forall i :: 1 <= i < |s| + 1 ==> states[i] == d.transition(states[i-1], s[i-1]);
                assert Accepted(d, s);
            } else {
                // Inductive case: Accept2(d, s) means Accept2(nextDFA, s[1..]) is true
                var nextState := d.transition(d.startState, s[0]);
                var nextDFA := DFA(d.states, d.alphabet, d.transition, nextState, d.acceptStates);
                assert ValidDfa(nextDFA);
                assert ValidString(nextDFA, s[1..]);
                assert Accept2(nextDFA, s[1..]);
                
                // By induction, there exists a state sequence for s[1..] starting from nextState
                Accept2ImpliesAccepted(nextDFA, s[1..]);
                assert Accepted(nextDFA, s[1..]);
                
                // Extract the witness sequence for s[1..]
                var tailStates: seq<State> :| |tailStates| == |s[1..]| + 1 && 
                                             tailStates[0] == nextState && 
                                             tailStates[|s[1..]|] in d.acceptStates && 
                                             (forall i :: 0 <= i < |tailStates| ==> tailStates[i] in d.states) && 
                                             (forall i :: 1 <= i < |s[1..]| + 1 ==> tailStates[i] == d.transition(tailStates[i-1], s[1..][i-1]));
                
                // Build the full state sequence by prepending d.startState
                var states := [d.startState] + tailStates;
                assert |states| == |s| + 1;
                assert states[0] == d.startState;
                assert states[|s|] == tailStates[|s[1..]|];
                assert states[|s|] in d.acceptStates;
                assert forall i :: 0 <= i < |states| ==> states[i] in d.states;
                assert forall i :: 1 <= i < |s| + 1 ==> states[i] == d.transition(states[i-1], s[i-1]);
                assert Accepted(d, s);
            }
        }
    }

    lemma AcceptedImpliesAccept2<State(!new,==), Alphabet(==)>(d: DFA<State, Alphabet>, s: seq<Alphabet>)
        requires ValidDfa(d) && ValidString(d, s)
        ensures Accepted(d, s) ==> Accept2(d, s)
        decreases |s|
    {
        if Accepted(d, s) {
            if |s| == 0 {
                // Base case: Accepted(d, []) means d.startState in d.acceptStates
                var states: seq<State> :| |states| == |s| + 1 && 
                                         states[0] == d.startState && 
                                         states[|s|] in d.acceptStates && 
                                         (forall i :: 0 <= i < |states| ==> states[i] in d.states) && 
                                         (forall i :: 1 <= i < |s| + 1 ==> states[i] == d.transition(states[i-1], s[i-1]));
                assert states == [d.startState];
                assert d.startState in d.acceptStates;
                assert Accept2(d, s);
            } else {
                // Inductive case: Extract witness sequence for full string
                var states: seq<State> :| |states| == |s| + 1 && 
                                         states[0] == d.startState && 
                                         states[|s|] in d.acceptStates && 
                                         (forall i :: 0 <= i < |states| ==> states[i] in d.states) && 
                                         (forall i :: 1 <= i < |s| + 1 ==> states[i] == d.transition(states[i-1], s[i-1]));
                
                // The first transition gives us the next state
                var nextState := states[1];
                assert nextState == d.transition(d.startState, s[0]);
                assert nextState in d.states;
                
                // Build the tail sequence for s[1..]
                var tailStates := states[1..];
                assert |tailStates| == |s[1..]| + 1;
                assert tailStates[0] == nextState;
                assert tailStates[|s[1..]|] == states[|s|];
                assert tailStates[|s[1..]|] in d.acceptStates;
                assert forall i :: 0 <= i < |tailStates| ==> tailStates[i] in d.states;
                assert forall i :: 1 <= i < |s[1..]| + 1 ==> tailStates[i] == d.transition(tailStates[i-1], s[1..][i-1]);
                
                // This shows Accepted(nextDFA, s[1..])
                var nextDFA := DFA(d.states, d.alphabet, d.transition, nextState, d.acceptStates);
                assert ValidDfa(nextDFA);
                assert ValidString(nextDFA, s[1..]);
                assert Accepted(nextDFA, s[1..]);
                
                // By induction, Accept2(nextDFA, s[1..]) is true
                AcceptedImpliesAccept2(nextDFA, s[1..]);
                assert Accept2(nextDFA, s[1..]);
                assert Accept2(d, s);
            }
        }
    }



    // lemma AcceptsEqual<State(==), Alphabet(==)>(d: DFA<State, Alphabet>, s: seq<Alphabet>, states: seq<State>, i: nat)
    //     requires ValidDfa(d) && ValidString(d, s)
    //     ensures Accepts(d, s, [d.startState], 0) == Accept2(d, s)
    // {
    //     if |s| == 0 {

    //     }else{
            
    //     }
    // }

    method Test() {
        var d: DFA<int, char> := DFA(
            {0, 1},
            {'a', 'b'},
            (s, a) =>
                if s == 0 && a == 'a' then 1
                else 0,
            0,
            {1}
        );
        assert ValidDfa(d);

        assert Accepts(d, "a", [0], 0);
        assert !Accepts(d, "b", [0], 0);
    }

    ghost function Language<State(!new), Alphabet(!new)>(d: DFA<State, Alphabet>): iset<seq<Alphabet>>
        requires ValidDfa(d)
    {
        iset w: seq<Alphabet> | ValidString(d, w) && Accepted(d, w)
    }

    // A language L is regular if it can be recognized by some DFA
    ghost predicate IsRegularLanguage<State(!new), Alphabet(!new)>(L: iset<seq<Alphabet>>, alphabet: set<Alphabet>)
    {
        exists dfa: DFA<State, Alphabet> :: 
            ValidDfa(dfa) && 
            dfa.alphabet == alphabet &&
            L == Language(dfa)
    }

    // Construction of a DFA that recognizes the union of two languages
    ghost function UnionDfa<State1(!new), State2(!new), Alphabet(!new)>(d1: DFA<State1, Alphabet>, d2: DFA<State2, Alphabet>): DFA<(State1, State2), Alphabet>
        requires ValidDfa(d1) && ValidDfa(d2)
        requires d1.alphabet == d2.alphabet
    {
        DFA(
            // States: Cartesian product of the two state sets
            set s1, s2 | s1 in d1.states && s2 in d2.states :: (s1, s2),
            
            // Alphabet: same as both DFAs
            d1.alphabet,
            
            // Transition function: apply both transitions in parallel
            (state: (State1, State2), a: Alphabet) => (d1.transition(state.0, a), d2.transition(state.1, a)),
            
            // Start state: pair of both start states
            (d1.startState, d2.startState),
            
            // Accept states: pairs where AT LEAST ONE component is accepting (union)
            set s1, s2 | s1 in d1.states && s2 in d2.states && (s1 in d1.acceptStates || s2 in d2.acceptStates) :: (s1, s2)
        )
    }

    // Lemma proving that the UnionDfa is valid when the input DFAs are valid
    lemma UnionDfaValid<State1(!new), State2(!new), Alphabet(!new)>(d1: DFA<State1, Alphabet>, d2: DFA<State2, Alphabet>)
        requires ValidDfa(d1) && ValidDfa(d2)
        requires d1.alphabet == d2.alphabet
        ensures ValidDfa(UnionDfa(d1, d2))
    {
        var unionDFA := UnionDfa(d1, d2);
        
        // Prove start state is in states
        assert unionDFA.startState == (d1.startState, d2.startState);
        assert d1.startState in d1.states && d2.startState in d2.states;
        assert unionDFA.startState in unionDFA.states;
        
        // Prove accept states are subset of states
        assert unionDFA.acceptStates <= unionDFA.states;
        
        // Prove valid transition function
        assert ValidTransitionFunction(unionDFA);
    }

    // Main theorem: Union of two regular languages is regular
    lemma UnionOfRegularLanguagesIsRegular<State(!new),Alphabet(!new)>(
        L1: iset<seq<Alphabet>>, 
        L2: iset<seq<Alphabet>>, 
        alphabet: set<Alphabet>)
        requires IsRegularLanguage<State, Alphabet>(L1, alphabet)
        requires IsRegularLanguage<State, Alphabet>(L2, alphabet)
        ensures IsRegularLanguage<(State, State), Alphabet>(L1 + L2, alphabet)
    {
        // Extract witness DFAs for L1 and L2
        var dfa1: DFA<State, Alphabet> :| ValidDfa(dfa1) && dfa1.alphabet == alphabet && L1 == Language(dfa1);
        var dfa2: DFA<State, Alphabet> :| ValidDfa(dfa2) && dfa2.alphabet == alphabet && L2 == Language(dfa2);
        
        // Construct the union DFA
        var unionDFA := UnionDfa(dfa1, dfa2);
        
        // Prove the union DFA is valid
        UnionDfaValid(dfa1, dfa2);
        assert ValidDfa(unionDFA);
        assert unionDFA.alphabet == alphabet;
        
        // Prove that the union DFA recognizes exactly L1 ∪ L2
        UnionDfaCorrectness(dfa1, dfa2, L1, L2);
        assert L1 + L2 == Language(unionDFA);
        
        // Therefore L1 ∪ L2 is regular
        assert IsRegularLanguage<(State, State), Alphabet>(L1 + L2, alphabet);
    }

    // Helper lemma: The union DFA recognizes exactly the union of the languages
    lemma UnionDfaCorrectness<State1(!new), State2(!new), Alphabet(!new)>(
        dfa1: DFA<State1, Alphabet>, 
        dfa2: DFA<State2, Alphabet>, 
        L1: iset<seq<Alphabet>>, 
        L2: iset<seq<Alphabet>>)
        requires ValidDfa(dfa1) && ValidDfa(dfa2)
        requires dfa1.alphabet == dfa2.alphabet
        requires L1 == Language(dfa1)
        requires L2 == Language(dfa2)
        ensures L1 + L2 == Language(UnionDfa(dfa1, dfa2))
    {
        var unionDFA := UnionDfa(dfa1, dfa2);
        
        // Prove both directions of the equality
        forall w: seq<Alphabet> 
            ensures w in (L1 + L2) <==> w in Language(unionDFA)
        {
            if ValidString(unionDFA, w) {
                // If w is in L1 ∪ L2, then it's accepted by unionDFA
                if w in L1 + L2 {
                    UnionDfaAcceptsUnion(dfa1, dfa2, w);
                    assert w in Language(unionDFA);
                }
                
                // If w is accepted by unionDFA, then it's in L1 ∪ L2
                if w in Language(unionDFA) {
                    UnionDfaOnlyAcceptsUnion(dfa1, dfa2, w);
                    assert w in L1 + L2;
                }
            }
        }
    }

    // Function to compute the state sequence for any string in a DFA
    ghost function ComputeStateSequence<State(!new), Alphabet(!new)>(d: DFA<State, Alphabet>, w: seq<Alphabet>): seq<State>
        requires ValidDfa(d) && ValidString(d, w)
        ensures |ComputeStateSequence(d, w)| == |w| + 1
        ensures ComputeStateSequence(d, w)[0] == d.startState
        ensures forall i :: 0 <= i < |ComputeStateSequence(d, w)| ==> ComputeStateSequence(d, w)[i] in d.states
        ensures forall i :: 1 <= i < |w| + 1 ==> ComputeStateSequence(d, w)[i] == d.transition(ComputeStateSequence(d, w)[i-1], w[i-1])
        decreases |w|
    {
        if |w| == 0 then
            [d.startState]
        else
            var nextState := d.transition(d.startState, w[0]);
            var newDFA := DFA(d.states, d.alphabet, d.transition, nextState, d.acceptStates);
            var restSequence := ComputeStateSequence(newDFA, w[1..]);
            [d.startState] + restSequence
    }

    // Lemma: The computed state sequence has all states in the DFA
    lemma ComputeStateSequenceValid<State(!new), Alphabet(!new)>(d: DFA<State, Alphabet>, w: seq<Alphabet>)
        requires ValidDfa(d) && ValidString(d, w)
        ensures var states := ComputeStateSequence(d, w);
                |states| == |w| + 1 &&
                states[0] == d.startState &&
                (forall i :: 0 <= i < |states| ==> states[i] in d.states) &&
                (forall i :: 1 <= i < |w| + 1 ==> states[i] == d.transition(states[i-1], w[i-1]))
    {
        var states := ComputeStateSequence(d, w);
        StateSequenceInDFA(d, w, states);
    }

    // Lemma: If a string is accepted, then the computed sequence ends in an accept state
    lemma ComputeStateSequenceAccepting<State(!new), Alphabet(!new)>(d: DFA<State, Alphabet>, w: seq<Alphabet>)
        requires ValidDfa(d) && ValidString(d, w)
        requires Accepted(d, w)
        ensures ComputeStateSequence(d, w)[|w|] in d.acceptStates
    {
        var acceptingStates: seq<State> :| |acceptingStates| == |w| + 1 &&
                                        acceptingStates[0] == d.startState &&
                                        (forall i :: 0 <= i < |acceptingStates| ==> acceptingStates[i] in d.states) &&
                                        (forall i :: 1 <= i < |w| + 1 ==> acceptingStates[i] == d.transition(acceptingStates[i-1], w[i-1])) &&
                                        acceptingStates[|w|] in d.acceptStates;
        assert ValidString(d, w);
        assert Accepted(d, w);
        var states := ComputeStateSequence(d, w);
        UniqueStateSequence(d, w, acceptingStates, states);
        // The existence of an accepting sequence and determinism implies our computed sequence is accepting
        assert states[|w|] in d.acceptStates;
    }

    // Helper lemma: Union DFA simulates both component DFAs in parallel
    lemma UnionDfaSimulatesParallel<State1(!new), State2(!new), Alphabet(!new)>(
        dfa1: DFA<State1, Alphabet>, 
        dfa2: DFA<State2, Alphabet>, 
        w: seq<Alphabet>,
        unionStates: seq<(State1, State2)>,
        states1: seq<State1>,
        states2: seq<State2>,
        i: nat)
        requires ValidDfa(dfa1) && ValidDfa(dfa2)
        requires dfa1.alphabet == dfa2.alphabet
        requires ValidString(dfa1, w) && ValidString(dfa2, w)
        requires |unionStates| == |w| + 1
        requires |states1| == |w| + 1
        requires |states2| == |w| + 1
        requires 0 <= i <= |w|
        requires unionStates[0] == (dfa1.startState, dfa2.startState)
        requires states1[0] == dfa1.startState
        requires states2[0] == dfa2.startState
        requires forall j :: 1 <= j < i + 1 ==> unionStates[j] == (states1[j], states2[j])
        requires forall j :: 1 <= j < i + 1 ==> states1[j] == dfa1.transition(states1[j-1], w[j-1])
        requires forall j :: 1 <= j < i + 1 ==> states2[j] == dfa2.transition(states2[j-1], w[j-1])
        ensures forall j :: 1 <= j < i + 1 ==> unionStates[j] == (dfa1.transition(unionStates[j-1].0, w[j-1]), dfa2.transition(unionStates[j-1].1, w[j-1]))
        ensures forall j :: 0 <= j < i + 1 ==> unionStates[j] == (states1[j], states2[j])
        decreases i
    {
        if i == 0 {
            // Base case: initial states match
            assert unionStates[0] == (dfa1.startState, dfa2.startState);
            assert states1[0] == dfa1.startState;
            assert states2[0] == dfa2.startState;
            assert unionStates[0] == (states1[0], states2[0]);
        } else {
            // Inductive case: assume parallel simulation holds up to i-1, prove for i
            UnionDfaSimulatesParallel(dfa1, dfa2, w, unionStates, states1, states2, i - 1);
            
            // Now prove that the i-th transition is correct
            assert unionStates[i] == (states1[i], states2[i]);
            assert states1[i] == dfa1.transition(states1[i-1], w[i-1]);
            assert states2[i] == dfa2.transition(states2[i-1], w[i-1]);
            assert unionStates[i-1] == (states1[i-1], states2[i-1]);
            
            // Therefore the union transition is correct
            assert unionStates[i] == (dfa1.transition(unionStates[i-1].0, w[i-1]), dfa2.transition(unionStates[i-1].1, w[i-1]));
        }
    }

    // Helper lemma: If dfa1 accepts w, then union DFA accepts w
    lemma UnionDfaAcceptsFromDFA1<State1(!new), State2(!new), Alphabet(!new)>(
        dfa1: DFA<State1, Alphabet>, 
        dfa2: DFA<State2, Alphabet>, 
        w: seq<Alphabet>)
        requires ValidDfa(dfa1) && ValidDfa(dfa2)
        requires dfa1.alphabet == dfa2.alphabet
        requires ValidString(dfa1, w) && ValidString(dfa2, w)
        requires Accepted(dfa1, w)
        ensures Accepted(UnionDfa(dfa1, dfa2), w)
    {
        var unionDFA := UnionDfa(dfa1, dfa2);
        
        // Compute the state sequences for both DFAs
        var states1 := ComputeStateSequence(dfa1, w);
        var states2 := ComputeStateSequence(dfa2, w);
        
        // Construct the union state sequence
        var unionStates := seq(|w| + 1, i requires   0 <= i < |w| + 1 => (states1[i], states2[i]));
        
        // Prove that this is a valid accepting sequence for the union DFA
        assert |unionStates| == |w| + 1;
        assert unionStates[0] == (dfa1.startState, dfa2.startState) == unionDFA.startState;
        
        // Since dfa1 accepts w, its final state is accepting
        ComputeStateSequenceAccepting(dfa1, w);
        assert states1[|w|] in dfa1.acceptStates;
        
        // The final state has the first component accepting, so it's in unionDFA.acceptStates
        assert unionStates[|w|] == (states1[|w|], states2[|w|]);
        assert unionStates[|w|] in unionDFA.acceptStates;
        
        
        // Therefore the union DFA accepts w
        assert Accepted(unionDFA, w);
    }

    // Helper lemma: If dfa2 accepts w, then union DFA accepts w
    lemma UnionDfaAcceptsFromDFA2<State1(!new), State2(!new), Alphabet(!new)>(
        dfa1: DFA<State1, Alphabet>, 
        dfa2: DFA<State2, Alphabet>, 
        w: seq<Alphabet>)
        requires ValidDfa(dfa1) && ValidDfa(dfa2)
        requires dfa1.alphabet == dfa2.alphabet
        requires ValidString(dfa1, w) && ValidString(dfa2, w)
        requires Accepted(dfa2, w)
        ensures Accepted(UnionDfa(dfa1, dfa2), w)
    {
        var unionDFA := UnionDfa(dfa1, dfa2);
        
        // Compute the state sequences for both DFAs
        var states1 := ComputeStateSequence(dfa1, w);
        var states2 := ComputeStateSequence(dfa2, w);
        
        // Construct the union state sequence
        var unionStates := seq(|w| + 1, i requires 0 <= i < |w| + 1 => (states1[i], states2[i]));
        
        // Prove that this is a valid accepting sequence for the union DFA
        assert |unionStates| == |w| + 1;
        assert unionStates[0] == (dfa1.startState, dfa2.startState) == unionDFA.startState;
        
        // Since dfa2 accepts w, its final state is accepting
        ComputeStateSequenceAccepting(dfa2, w);
        assert states2[|w|] in dfa2.acceptStates;
        
        // The final state has the second component accepting, so it's in unionDFA.acceptStates
        assert unionStates[|w|] == (states1[|w|], states2[|w|]);
        assert unionStates[|w|] in unionDFA.acceptStates;
        
        
        // Therefore the union DFA accepts w
        assert Accepted(unionDFA, w);
    }

    // Helper lemma: If a string is in L1 ∪ L2, then it's accepted by the union DFA
    lemma UnionDfaAcceptsUnion<State1(!new), State2(!new), Alphabet(!new)>(
        dfa1: DFA<State1, Alphabet>, 
        dfa2: DFA<State2, Alphabet>, 
        w: seq<Alphabet>)
        requires ValidDfa(dfa1) && ValidDfa(dfa2)
        requires dfa1.alphabet == dfa2.alphabet
        requires ValidString(dfa1, w) && ValidString(dfa2, w)
        requires Accepted(dfa1, w) || Accepted(dfa2, w)
        ensures Accepted(UnionDfa(dfa1, dfa2), w)
    {
        var unionDFA := UnionDfa(dfa1, dfa2);
        
        // Case analysis: either dfa1 accepts w, or dfa2 accepts w (or both)
        if Accepted(dfa1, w) {
            // Case 1: dfa1 accepts w
            UnionDfaAcceptsFromDFA1(dfa1, dfa2, w);
            assert Accepted(unionDFA, w);
        } else {
            // Case 2: dfa2 accepts w (since we know dfa1 || dfa2 accepts)
            assert Accepted(dfa2, w);
            UnionDfaAcceptsFromDFA2(dfa1, dfa2, w);
            assert Accepted(unionDFA, w);
        }
    }

    // Helper lemma: If a string is accepted by the union DFA, then it's in L1 ∪ L2  
    lemma UnionDfaOnlyAcceptsUnion<State1(!new), State2(!new), Alphabet(!new)>(
        dfa1: DFA<State1, Alphabet>, 
        dfa2: DFA<State2, Alphabet>, 
        w: seq<Alphabet>)
        requires ValidDfa(dfa1) && ValidDfa(dfa2)
        requires dfa1.alphabet == dfa2.alphabet
        requires ValidString(UnionDfa(dfa1, dfa2), w)
        requires Accepted(UnionDfa(dfa1, dfa2), w)
        ensures Accepted(dfa1, w) || Accepted(dfa2, w)
    {
        var unionDFA := UnionDfa(dfa1, dfa2);
        
        // Since the union DFA accepts w, there exists a witness state sequence
        var unionStates: seq<(State1, State2)> :| 
            |unionStates| == |w| + 1 &&
            unionStates[0] == unionDFA.startState &&
            unionStates[|w|] in unionDFA.acceptStates &&
            (forall i :: 0 <= i < |unionStates| ==> unionStates[i] in unionDFA.states) &&
            (forall i :: 1 <= i < |w| + 1 ==> unionStates[i] == unionDFA.transition(unionStates[i-1], w[i-1]));
        
        // Extract the component state sequences
        var states1 := seq(|w| + 1, i requires 0 <= i < |w| + 1 => unionStates[i].0);
        var states2 := seq(|w| + 1, i requires 0 <= i < |w| + 1 => unionStates[i].1);
        
        // Prove these are valid state sequences for the component DFAs
        // assert |states1| == |w| + 1;
        // assert |states2| == |w| + 1;
        // assert states1[0] == unionStates[0].0 == unionDFA.startState.0 == dfa1.startState;
        // assert states2[0] == unionStates[0].1 == unionDFA.startState.1 == dfa2.startState;
        
        // Prove transitions are correct for component DFAs
        forall i | 1 <= i < |w| + 1
            ensures states1[i] == dfa1.transition(states1[i-1], w[i-1])
            ensures states2[i] == dfa2.transition(states2[i-1], w[i-1])
        {
            // assert unionStates[i] == unionDFA.transition(unionStates[i-1], w[i-1]);
            // assert unionStates[i] == (dfa1.transition(unionStates[i-1].0, w[i-1]), dfa2.transition(unionStates[i-1].1, w[i-1]));
            // assert states1[i] == unionStates[i].0 == dfa1.transition(unionStates[i-1].0, w[i-1]) == dfa1.transition(states1[i-1], w[i-1]);
            // assert states2[i] == unionStates[i].1 == dfa2.transition(unionStates[i-1].1, w[i-1]) == dfa2.transition(states2[i-1], w[i-1]);
        }
        
        // Prove all states are valid in their respective DFAs
        forall i | 0 <= i < |states1|
            ensures states1[i] in dfa1.states
            ensures states2[i] in dfa2.states
        {
            assert unionStates[i] in unionDFA.states;
            assert states1[i] == unionStates[i].0;
            assert states2[i] == unionStates[i].1;
            assert unionStates[i].0 in dfa1.states;
            assert unionStates[i].1 in dfa2.states;
        }
        
        // The final state of unionDFA is accepting
        assert unionStates[|w|] in unionDFA.acceptStates;
        var finalState1 := states1[|w|];
        var finalState2 := states2[|w|];
        assert unionStates[|w|] == (finalState1, finalState2);
        
        // By definition of unionDFA.acceptStates, either finalState1 or finalState2 is accepting
        assert (finalState1 in dfa1.acceptStates) || (finalState2 in dfa2.acceptStates);
        
        // Case analysis: either dfa1 accepts w, or dfa2 accepts w (or both)
        if finalState1 in dfa1.acceptStates {
            // dfa1 accepts w
            assert Accepted(dfa1, w);
        } else {
            // dfa2 accepts w (since we know at least one must accept)
            assert finalState2 in dfa2.acceptStates;
            assert Accepted(dfa2, w);
        }
        
        // Therefore: Accepted(dfa1, w) || Accepted(dfa2, w)
        assert Accepted(dfa1, w) || Accepted(dfa2, w);
    }


}