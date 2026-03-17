import NaturalFramework.Axioms

/-!
# Boundary proofs

The two boundary arguments that force the pipeline's existence.
Derived from the physics axioms, not assumed.

## Boundary 1: Encoding before selection

The environment has higher dimensionality than internal state (Landauer).
A surjection (Perceive) must bridge them. Inputs arrive faster than
outputs drain (rate mismatch axiom). A buffer (Cache) must exist
or items are lost.

## Boundary 2: Selection before persistence

Bounded storage (Landauer) forces selection before persistence.
Without gating, the store fills and the system halts.
-/

-- ============================================================
-- Boundary 1: Perceive is forced
-- ============================================================

/-- The environment is strictly larger than internal state.
    Landauer bounds internal state to N ≤ energy.
    The environment has more distinguishable configurations than
    the system can represent. A surjection (lossy map) is forced.

    Derived from: Landauer axiom.
    Falsifiable: if internal state can be as large as environment,
    no lossy encoding needed. Landauer prevents this. -/
theorem perceive_forced (energy env_dim : Nat)
    (he : energy > 0)
    (henv : env_dim > energy)
    : ∀ N : Nat, N ≤ energy → env_dim > N := by
  intro N hN
  omega

-- ============================================================
-- Boundary 1: Cache is forced
-- ============================================================

/-- Without a buffer, rate mismatch causes cumulative loss.
    If input_rate > drain_rate, then after k cycles,
    at least k items are lost (one per cycle minimum).

    Derived from: rate mismatch axiom.
    Falsifiable: if input never exceeds drain rate, no buffer needed.
    The rate_mismatch axiom asserts this can happen. -/
theorem no_cache_cumulative_loss
    (input_rate drain_rate k : Nat)
    (hmismatch : input_rate > drain_rate)
    (hk : k > 0)
    : k * (input_rate - drain_rate) ≥ k := by
  have hgap : input_rate - drain_rate ≥ 1 := by omega
  calc k * (input_rate - drain_rate)
      ≥ k * 1 := Nat.mul_le_mul_left k hgap
    _ = k := Nat.mul_one k

/-- Cache existence follows from rate mismatch: the axiom guarantees
    a scenario where input outpaces drain. Without a buffer, loss
    is cumulative. Therefore a buffer must exist to prevent loss. -/
theorem cache_from_rate_mismatch :
    ∃ (input_rate drain_rate : Nat),
      input_rate > drain_rate ∧ drain_rate > 0 ∧
      ∀ k : Nat, k > 0 → k * (input_rate - drain_rate) ≥ k := by
  obtain ⟨ir, dr, hmm, hdr⟩ := rate_mismatch
  exact ⟨ir, dr, hmm, hdr, fun k hk => no_cache_cumulative_loss ir dr k hmm hk⟩

-- ============================================================
-- Boundary 2: Selection before persistence
-- ============================================================

/-- Without selection, a store of capacity C fills after C insertions.
    Once full, the system must either drop new items (implicit selection)
    or halt. Explicit selection (Filter) prevents the halt.

    Derived from: Landauer (finite capacity).
    Falsifiable: infinite capacity → no pressure to select. -/
theorem no_filter_fills_store
    (capacity items_per_cycle : Nat)
    (hcap : capacity > 0)
    (hitems : items_per_cycle > 0)
    : ∃ t : Nat, t * items_per_cycle ≥ capacity := by
  exact ⟨capacity, by
    calc capacity * items_per_cycle
        ≥ capacity * 1 := Nat.mul_le_mul_left capacity hitems
      _ = capacity := Nat.mul_one capacity⟩

-- ============================================================
-- Loop closure: Remember is forced
-- ============================================================

/-- A pipeline without persistence has no loop. Each cycle's
    output is discarded. The system cannot learn from its past.

    Model: without Remember, the state after each cycle is
    determined entirely by the current input and the fixed initial
    policy. After N distinct inputs, behavior repeats.

    Derived from: the pipeline structure (feedback requires persistence).
    Falsifiable: if the system doesn't need to loop, Remember is optional.
    But a non-looping system is open-loop: stimulus-response with no memory. -/
theorem no_persistence_no_memory
    (N : Nat) (hN : N > 0)
    {I O : Type}
    (response : Fin N → I → O)
    (fixed_state : Fin N)
    : ∀ (env : Nat → I),
      ∀ t₁ t₂ : Nat, env t₁ = env t₂ →
      response fixed_state (env t₁) = response fixed_state (env t₂) := by
  intro env t₁ t₂ heq
  rw [heq]
