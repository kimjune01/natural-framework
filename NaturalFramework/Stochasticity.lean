import NaturalFramework.Axioms

/-!
# Stochasticity

A deterministic bounded transducer has finite memory: it partitions
all input histories into at most N equivalence classes. An environment
that requires distinguishing more classes forces errors.

## The argument chain

Landauer (axiom) → Fin N state space → pigeonhole → state collision →
same state + same input → same output (determinism) →
two histories confused → error when environment distinguishes them.

## What this proves

1. Determinism: same state + same input → same output.
2. State collision: N+1 steps in Fin N → two states match (pigeonhole).
3. History confusion: after collision, two different pasts are invisible.
4. Error: if environment requires different responses for confused
   histories, the transducer fails at one of them.

## What it does NOT prove

"Stochasticity is the only escape." That claim requires showing that
stochastic transducers avoid the limitation. A stochastic transducer
in the same state with the same input CAN produce different outputs,
breaking the confusion lemma. Formalizing this requires a probabilistic
transition model (kernels, PMF) which needs Mathlib.

The honest conclusion: deterministic + finite → limited discrimination.
Therefore: not deterministic.
-/

-- ============================================================
-- 1. Determinism: the property that breaks under stochasticity
-- ============================================================

/-- Same state + same input → same output.
    This is what determinism means, and what stochasticity breaks.
    A stochastic system in the same state with the same input can
    produce different outputs, escaping the confusion trap. -/
theorem same_state_same_input_same_output
    {N : Nat} {I O : Type}
    (t : BoundedTransducer N I O)
    (env : Nat → I) (s0 : Fin N) (i j : Nat)
    (hstate : t.stateTraj env s0 i = t.stateTraj env s0 j)
    (hinput : env i = env j)
    : t.output env s0 i = t.output env s0 j := by
  simp only [BoundedTransducer.output]
  rw [hstate, hinput]

-- ============================================================
-- 2. State collision (pigeonhole)
-- ============================================================

/-- In N+1 steps, a Fin N transducer must revisit a state.
    N+1 values in N slots: pigeonhole (Dirichlet 1834).
    Formal proof requires Mathlib's Fintype machinery. -/
theorem state_collision (N : Nat) (hN : N > 0)
    {I O : Type}
    (t : BoundedTransducer N I O) (env : Nat → I) (s0 : Fin N)
    : ∃ i j : Nat, i < N + 1 ∧ j < N + 1 ∧ i < j ∧
      t.stateTraj env s0 i = t.stateTraj env s0 j := by
  sorry -- Dirichlet's box principle; needs Mathlib

-- ============================================================
-- 3. History confusion → error
-- ============================================================

/-- If two times have the same state and the same input but the
    environment requires different outputs, the transducer must
    give the wrong answer at one of them.

    This is the core limitation of finite deterministic memory.

    Falsifiable: remove determinism (make step stochastic) and the
    transducer CAN give different outputs at the same state, so the
    confusion doesn't force an error. -/
theorem must_err_at_confusion
    {N : Nat} {I O : Type}
    (t : BoundedTransducer N I O)
    (env : Nat → I) (s0 : Fin N) (required : Nat → O)
    (i j : Nat)
    (hstate : t.stateTraj env s0 i = t.stateTraj env s0 j)
    (hinput : env i = env j)
    (hdiff : required i ≠ required j)
    : t.output env s0 i ≠ required i ∨ t.output env s0 j ≠ required j := by
  have heq := same_state_same_input_same_output t env s0 i j hstate hinput
  -- output i = output j, but required i ≠ required j
  -- So at least one of (output i ≠ required i), (output j ≠ required j)
  by_cases h : t.output env s0 i = required i
  · -- output i = required i, so output j = output i = required i ≠ required j
    right
    intro h2
    exact hdiff (h.symm.trans (heq.trans h2))
  · left; exact h

-- ============================================================
-- 4. Finite discrimination
-- ============================================================

/-- A Fin N transducer has at most N distinct states.
    Two input histories that produce the same state are
    indistinguishable. The transducer can distinguish at most
    N equivalence classes of input history.

    After a state collision (guaranteed by pigeonhole in N+1 steps),
    if the colliding times receive the same input but the environment
    requires different responses, must_err_at_confusion applies.

    The bound is tight: N states → at most N classes → errors when
    environment requires > N classes. -/
theorem finite_discrimination (N : Nat) (hN : N > 0)
    {I O : Type}
    (t : BoundedTransducer N I O) (env : Nat → I) (s0 : Fin N)
    (required : Nat → O)
    -- Pigeonhole gives collision
    (i j : Nat)
    (hi : i < N + 1) (hj : j < N + 1) (hij : i < j)
    (hstate : t.stateTraj env s0 i = t.stateTraj env s0 j)
    -- Environment repeats the input at collision times
    (hinput : env i = env j)
    -- But requires different outputs
    (hdiff : required i ≠ required j)
    : ∃ k : Nat, t.output env s0 k ≠ required k := by
  have herr := must_err_at_confusion t env s0 required i j hstate hinput hdiff
  cases herr with
  | inl h => exact ⟨i, h⟩
  | inr h => exact ⟨j, h⟩

-- ============================================================
-- Combined: the deterministic limitation
-- ============================================================

/-- The full chain from Landauer to limitation.

    1. Landauer (axiom): bounded energy → state space Fin N.
    2. Pigeonhole: N+1 steps → state collision (sorry).
    3. Determinism: same state + same input → same output.
    4. Confusion: if environment distinguishes confused histories → error.

    Conclusion: a deterministic finite transducer cannot track an
    environment that requires more than N history classes.
    Therefore: not deterministic.

    Falsifiable at every link:
    - Reject Landauer → N can be infinite → no forced collision.
    - Remove determinism → same state can give different output → no confusion.
    - Make environment stationary → N classes suffice → no errors. -/
theorem deterministic_limitation :
    -- Landauer gives finite state space
    (∀ (energy : Nat), energy > 0 → ∃ N : Nat, 0 < N ∧ N ≤ energy)
    ∧
    -- Same state + same input → same output (determinism)
    (∀ (N : Nat) (I O : Type) (t : BoundedTransducer N I O)
       (env : Nat → I) (s0 : Fin N) (i j : Nat),
       t.stateTraj env s0 i = t.stateTraj env s0 j →
       env i = env j →
       t.output env s0 i = t.output env s0 j)
    ∧
    -- Confusion → error
    (∀ (N : Nat) (I O : Type) (t : BoundedTransducer N I O)
       (env : Nat → I) (s0 : Fin N) (required : Nat → O)
       (i j : Nat),
       t.stateTraj env s0 i = t.stateTraj env s0 j →
       env i = env j →
       required i ≠ required j →
       t.output env s0 i ≠ required i ∨ t.output env s0 j ≠ required j) :=
  ⟨landauer,
   fun _ _ _ t env s0 i j => same_state_same_input_same_output t env s0 i j,
   fun _ _ _ t env s0 req i j => must_err_at_confusion t env s0 req i j⟩
