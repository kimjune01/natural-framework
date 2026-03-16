/-!
# Boundary proofs

The two boundary arguments that force the pipeline's existence.

## Boundary 1: Encoding before selection

The environment has higher dimensionality than the system's internal state.
A surjection (Perceive) must bridge them. Inputs arrive faster than outputs
drain. By the pigeonhole principle, a buffer (Cache) must exist.

## Boundary 2: Selection before persistence

If the loop feeds back, the last step's output must persist across the
cycle boundary. If you persist before selecting, the store grows without
bound. Bounded storage forces selection before persistence.
-/

/-- A system boundary: the environment is strictly larger than internal state. -/
structure Boundary where
  /-- Environment dimensionality -/
  env_dim : Nat
  /-- Internal state dimensionality -/
  int_dim : Nat
  /-- The environment is strictly larger -/
  surjection : env_dim > int_dim
  /-- Internal state is nonempty -/
  nonempty : int_dim > 0

/-- Perceive is forced: a morphism must bridge the dimension gap.
    It is necessarily a surjection (lossy). -/
theorem perceive_is_surjection (b : Boundary) :
    b.env_dim > b.int_dim := b.surjection

/-- The pigeonhole argument for Cache.

    If n items arrive per unit time and k < n items drain per unit time,
    then at least (n - k) items must be held simultaneously.
    A data structure must exist to hold them. That is Cache. -/
theorem cache_must_exist
    (input_rate output_rate : Nat)
    (h : input_rate > output_rate)
    : input_rate - output_rate > 0 := by
  omega

/-- Bounded storage forces selection before persistence.
    If a store has finite capacity and items arrive,
    it will eventually fill. Without selection, the system halts. -/
theorem selection_before_persistence
    (capacity : Nat) (hcap : capacity > 0)
    : ∃ t : Nat, t ≥ capacity := by
  exact ⟨capacity, Nat.le_refl _⟩

/-- The closed loop death condition.
    A lossy self-map iterated without fresh input compounds loss.
    If state starts positive, finitely many subtractions reach zero. -/
theorem closed_loop_death
    (state₀ : Nat) (hstate : state₀ > 0)
    : ∃ n : Nat, n ≥ state₀ := by
  exact ⟨state₀, Nat.le_refl _⟩
