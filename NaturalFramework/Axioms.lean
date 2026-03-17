/-!
# System Axioms

The axioms that ground the Natural Framework. Each is empirically
falsifiable: reject any one and the dependent theorems break.

Lean tracks axiom usage. Any theorem that depends on these is marked
by the kernel. No hidden assumptions.

## The axioms

Four `axiom` declarations plus one predicate definition:

1. **Capacity bound** (axiom): bounded energy → bounded distinguishable states.
2. **Rate mismatch** (axiom): input can outpace processing.
3. **Non-stationarity** (def): environments change. A property, not a universal law.
4. **Positive loss** (axiom): bounded systems lose information each cycle.
5. **History matters** (axiom): tasks exist where context determines correct response.

## The contested sixth

These five constrain bounded systems. The sixth — what grounds
the base case of the induction — is a choice between two starting points:
- **Bottom-up**: life exists at time 0 (observation).
- **Top-down**: the universe's Attend is intentional (purpose).
Pick one, derive the other. See Induction.lean.
-/

-- ============================================================
-- Axiom 1: Capacity bound
-- ============================================================

/-- Bounded energy → bounded distinguishable states.
    Energy bounds the number of states a system can maintain.
    The bound feeds directly into the transducer's state space (Fin N).

    As a Lean axiom this is trivially satisfiable (pick N = 1). The
    physical content — that energy limits state capacity — lives in
    the interpretation, not the formalization. The axiom asserts the
    shape (finite bound exists) that downstream proofs require.

    Reject → infinite states → pigeonhole fails → no forced collision. -/
axiom capacity_bound (energy : Nat) (he : energy > 0) :
  ∃ N : Nat, 0 < N ∧ N ≤ energy

-- ============================================================
-- Axiom 2: Rate mismatch
-- ============================================================

/-- Input can arrive faster than the system can process.
    This is empirical: environments are richer than processors.

    Reject → input never exceeds processing rate →
    no buffer needed → Cache is optional. -/
axiom rate_mismatch :
  ∃ (input_rate drain_rate : Nat),
    input_rate > drain_rate ∧ drain_rate > 0

-- ============================================================
-- Axiom 3: Non-stationarity
-- ============================================================

/-- Environments change. Modeled as: the required response at some
    time t differs from what it was at time t + p for any period p.

    This is a condition on specific environments, not a universal law.
    We state it as a property that environments can have.

    Reject → environment is periodic → periodic behavior suffices →
    stochasticity is optional. -/
def NonStationary {O : Type} (required : Nat → O) (p : Nat) : Prop :=
  ∃ t, required t ≠ required (t + p)

-- ============================================================
-- Axiom 4: Positive loss per cycle
-- ============================================================

/-- Bounded systems lose information each cycle. At least some
    bits are irreversibly lost per processing step.

    As a Lean axiom this is trivially satisfiable (pick loss = 1).
    The physical content — that bounded processors cannot avoid
    information loss — lives in the interpretation. The axiom asserts
    the shape (positive loss exists) that downstream proofs require.

    Reject → lossless computation → closed loop survives. -/
axiom positive_loss : ∃ (loss : Nat), loss > 0

-- ============================================================
-- Axiom 5: History-dependent tasks exist
-- ============================================================

/-- A task is history-dependent when the correct response to the
    same input differs based on what happened before. -/
def HistoryDependent {I O : Type} (env : Nat → I) (required : Nat → O) : Prop :=
  ∃ t₁ t₂ : Nat, env t₁ = env t₂ ∧ required t₁ ≠ required t₂

/-- History-dependent tasks exist. The correct response to a stimulus
    can depend on context and past experience.

    Reject → all tasks are memoryless stimulus-response →
    persistence and policy-reading are unnecessary. -/
axiom history_matters :
  ∃ (env : Nat → Nat) (required : Nat → Nat),
    HistoryDependent env required

-- ============================================================
-- Bounded Transducer (the unified model)
-- ============================================================

/-- A bounded deterministic transducer: finite state space Fin N,
    processes an input stream, produces output.

    State space size N is bounded by capacity_bound.
    Step function is deterministic: (state, input) → (state, output).
    This is the single formal model that all proofs reference. -/
structure BoundedTransducer (N : Nat) (I O : Type) where
  /-- Transition function -/
  step : Fin N → I → Fin N × O

/-- State trajectory: states visited given input stream and initial state. -/
def BoundedTransducer.stateTraj {N : Nat} {I O : Type}
    (t : BoundedTransducer N I O) (env : Nat → I) (s0 : Fin N)
    : Nat → Fin N
  | 0 => s0
  | k + 1 => (t.step (t.stateTraj env s0 k) (env k)).1

/-- Output at time k: produced when processing input k from state k. -/
def BoundedTransducer.output {N : Nat} {I O : Type}
    (t : BoundedTransducer N I O) (env : Nat → I) (s0 : Fin N)
    (k : Nat) : O :=
  (t.step (t.stateTraj env s0 k) (env k)).2
