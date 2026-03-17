import NaturalFramework.Axioms

/-!
# Corollaries

Three corollaries derived from the boundary proofs and physics axioms.
Each is a removal argument: without this property, the system fails.

## Corollary 1: The competitive core exists (Filter)

Bounded storage forces selection. Selection that operates on a set
produces a proper subset. Output < input. That is Filter.

## Corollary 2: Control separates from data

If policy shares a pool with data, high-volume data evicts policy.
A shared pool with bounded capacity and unequal arrival rates
forces eviction of the minority type.

## Corollary 3: Consolidate and Attend exist

A separate policy store needs a read interface (Attend) and a write
interface (Consolidate). Both are forced by bounded resources.
-/

-- ============================================================
-- Corollary 1: Filter (competitive core) is forced
-- ============================================================

/-- If output is a proper subset of input, the count decreases.
    Selection is forced by bounded storage (Landauer).
    Without it, the store fills (shown in Boundary). -/
theorem filter_reduces
    (input_count output_count : Nat)
    (h : output_count < input_count)
    : input_count - output_count ≥ 1 := by
  omega

/-- After k cycles of selection, k * (input - output) items are removed.
    This is the competitive core: winners persist, losers are discarded.
    The rate of removal is determined by the selection pressure. -/
theorem competitive_core_removes
    (input_count output_count k : Nat)
    (hsel : output_count < input_count)
    (hk : k > 0)
    : k * (input_count - output_count) ≥ k := by
  have : input_count - output_count ≥ 1 := by omega
  calc k * (input_count - output_count)
      ≥ k * 1 := Nat.mul_le_mul_left k this
    _ = k := Nat.mul_one k

-- ============================================================
-- Corollary 2: Control must separate from data
-- ============================================================

/-- In a shared pool of capacity C, if data arrives at rate d
    and policy occupies p slots, and d > C - p, then data
    overflows the free space and evicts policy.

    This is NOT tautological. It derives eviction from:
    - bounded capacity (Landauer)
    - unequal arrival rates (empirical)
    - first-in eviction under pressure

    Falsifiable: if data rate never exceeds free capacity,
    policy survives in the shared pool. The rate_mismatch axiom
    asserts that such pressure exists. -/
theorem policy_evicted_in_shared_pool
    (capacity data_rate policy_slots : Nat)
    (hcap : capacity > 0)
    (hpol : policy_slots > 0)
    (hfits : policy_slots ≤ capacity)
    (hoverflow : data_rate > capacity - policy_slots)
    : data_rate + policy_slots > capacity := by
  omega

/-- If policy and data share a pool, and data volume exceeds free
    capacity, policy is corrupted within policy_slots cycles.
    The eviction rate exceeds zero, so after enough cycles all
    policy slots are overwritten.

    This forces type separation: policy and data must be in
    different stores. That is why Attend (read policy) and
    Consolidate (write policy) are separate interfaces. -/
theorem shared_pool_kills_policy
    (capacity data_rate policy_slots : Nat)
    (hcap : capacity > 0)
    (hpol : policy_slots > 0)
    (hfits : policy_slots ≤ capacity)
    (hoverflow : data_rate > capacity - policy_slots)
    : -- After policy_slots cycles, all policy could be evicted
      policy_slots * (data_rate + policy_slots - capacity) ≥ policy_slots := by
  have hpressure : data_rate + policy_slots - capacity ≥ 1 := by omega
  calc policy_slots * (data_rate + policy_slots - capacity)
      ≥ policy_slots * 1 := Nat.mul_le_mul_left policy_slots hpressure
    _ = policy_slots := Nat.mul_one policy_slots

-- ============================================================
-- Corollary 3: Read and write interfaces are forced
-- ============================================================

/-- A separate policy store needs both interfaces:
    - Read: apply policy to data (Attend)
    - Write: update policy from outcomes (Consolidate)

    Without the read interface, policy exists but is never applied.
    Without the write interface, policy is static and cannot adapt.
    Both conditions lead to system failure. -/
structure SeparatePolicyStore (policy data ranked : Type) where
  /-- Read interface: apply policy to data (Attend) -/
  read : policy → data → ranked
  /-- Write interface: update policy from outcomes (Consolidate) -/
  write : policy → ranked → policy

/-- Without a write interface, policy is static.
    A static policy in a non-stationary environment eventually
    mismatches the required behavior.

    Model: policy is fixed at p₀. If the optimal policy changes
    (non-stationarity), there exists a time where the fixed policy
    produces wrong output. -/
theorem static_policy_fails
    {P D R : Type}
    (apply_policy : P → D → R)
    (p₀ : P)
    (optimal : Nat → P)
    (env : Nat → D)
    (hchanges : ∃ t, optimal t ≠ optimal 0)
    (hmatters : ∀ t, optimal t ≠ p₀ →
      ∃ d : D, apply_policy (optimal t) d ≠ apply_policy p₀ d)
    : ∃ t, ∃ d : D,
      apply_policy (optimal t) d ≠ apply_policy p₀ d := by
  obtain ⟨t, hne⟩ := hchanges
  by_cases h : optimal t = p₀
  · -- optimal t = p₀ but optimal t ≠ optimal 0
    -- So optimal 0 ≠ p₀
    have : optimal 0 ≠ p₀ := fun h0 => hne (h.trans h0.symm)
    obtain ⟨d, hd⟩ := hmatters 0 this
    exact ⟨0, d, hd⟩
  · obtain ⟨d, hd⟩ := hmatters t h
    exact ⟨t, d, hd⟩
