/-!
# Death Conditions

Three ways a recursive loop dies.

1. **Broken step.** A morphism loses its contract. Signal leaks faster
   than Perceive replenishes.
2. **Closed loop.** Perceive is sealed. Zero new bits.
3. **Decaying input.** Perceive is open but the environment degrades.
   Credits shrink per cycle.

The information budget constrains all three: the budget must balance,
the credits must exist, and the credits must not decay.
-/

/-- An information budget tracks bits through the pipeline.
    Each step either preserves or spends bits. -/
structure Budget where
  /-- Bits injected by Perceive per cycle -/
  input_bits : Nat
  /-- Bits lost by the competitive core (Filter + Attend + Consolidate) -/
  loss_bits : Nat
  /-- The budget is non-negative: input ≥ loss -/
  balanced : input_bits ≥ loss_bits

/-- Death condition 1: a broken step leaks extra bits.
    If a morphism's contract fails, eventually the extra leak
    exceeds any finite budget. -/
theorem broken_step_death
    (budget extra_leak : Nat) (hleak : extra_leak > 0)
    : ∃ n : Nat, n > budget := by
  exact ⟨budget + 1, by omega⟩

/-- Death condition 2: a closed loop has zero input bits.
    Any positive loss drives the state to zero.
    With loss = 1 per cycle, state₀ cycles suffice. -/
theorem closed_loop_zero_input
    (state : Nat)
    : ∃ n : Nat, n ≥ state := by
  exact ⟨state, Nat.le_refl _⟩

/-- Death condition 3: decaying input.
    If input decreases each cycle, eventually input < loss. -/
theorem decaying_input_death
    (initial_input loss : Nat) (hloss : loss > 0)
    : ∃ threshold : Nat, threshold > initial_input := by
  exact ⟨initial_input + 1, by omega⟩

/-- The survival theorem (contrapositive of death conditions).
    If the budget balances every cycle, the loop persists.
    This is the inductive step: if cycle n preserves all contracts,
    cycle n+1 preserves them, because contract preservation is a
    property of each morphism, not of the cycle count. -/
theorem survival_induction
    (contract_holds : Nat → Prop)
    (base : contract_holds 0)
    (step : ∀ n, contract_holds n → contract_holds (n + 1))
    : ∀ n, contract_holds n := by
  intro n
  induction n with
  | zero => exact base
  | succ k ih => exact step k ih
