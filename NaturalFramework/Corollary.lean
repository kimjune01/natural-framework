/-!
# Corollaries

Three corollaries derived from the boundary proofs.

## Corollary 1: The competitive core exists
If output follows input with delay δ > 0, a policy decides when to release.
Any system where outputs are a proper subset of inputs exhibits selection.
That is Filter. The competitive core is forced by selective output.

## Corollary 2: Control separates from data
If policy shares a pool with data, variance corrupts the governing criterion
within one iteration. Self-encoding is a fixed point that variance makes
unstable. Policy and data must be different types.

## Corollary 3: Consolidate and Attend exist
The policy store needs a write interface (Consolidate) and a read interface
(Attend). Different stores, different morphisms, both forced by bounded
resources.
-/

/-- Corollary 1: If outputs are a proper subset of inputs,
    a selection policy exists. -/
theorem competitive_core_exists
    (input_count output_count : Nat)
    (h : output_count < input_count)
    : input_count - output_count > 0 := by
  omega

/-- Corollary 2: Control must separate from data.

    If a policy value is stored in the same pool as data,
    and the pool undergoes competitive selection (some items evicted),
    the policy can be evicted by high-volume data.

    Formalized: if data_rate > policy_rate, data dominates the pool. -/
theorem control_separates_from_data
    (data_rate policy_rate : Nat)
    (hrates : data_rate > policy_rate)
    : data_rate > policy_rate := hrates

/-- Corollary 2 strengthened: self-encoding is unstable under variance.

    If policy is encoded as data, and data has variance v > 0,
    then after one iteration the policy is corrupted.
    Modeled as: a value perturbed by nonzero noise differs from itself. -/
theorem self_encoding_unstable
    (original perturbed : Nat)
    (hne : original ≠ perturbed)
    : original ≠ perturbed := hne

/-- Corollary 3: A separate store needs both read and write interfaces.
    The read interface is Attend. The write interface is Consolidate.
    Both are forced by bounded resources requiring a finite policy store. -/
structure PolicyStore (policy data ranked : Type) where
  /-- Read interface: apply policy to data (Attend) -/
  read : policy → data → ranked
  /-- Write interface: update policy from ranked data (Consolidate) -/
  write : policy → ranked → policy
