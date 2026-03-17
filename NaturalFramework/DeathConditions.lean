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
    If a morphism's contract fails and leaks `extra_leak` bits per
    cycle, the cumulative leak eventually exceeds any finite budget.
    At cycle `budget + 1`: `(budget + 1) * extra_leak ≥ budget + 1 > budget`. -/
theorem broken_step_death
    (budget extra_leak : Nat) (hleak : extra_leak > 0)
    : ∃ n : Nat, n * extra_leak > budget := by
  refine ⟨budget + 1, ?_⟩
  have h : (budget + 1) * extra_leak ≥ budget + 1 :=
    calc (budget + 1) * extra_leak
        ≥ (budget + 1) * 1 := Nat.mul_le_mul_left _ hleak
      _ = budget + 1 := Nat.mul_one _
  omega

/-- Death condition 2: a closed loop has zero input bits.
    With positive loss per cycle, cumulative loss eventually depletes
    all state bits. At cycle `state`: `state * loss ≥ state`. -/
theorem closed_loop_zero_input
    (state loss : Nat) (hloss : loss > 0)
    : ∃ n : Nat, n * loss ≥ state := by
  exact ⟨state, by
    calc state * loss
        ≥ state * 1 := Nat.mul_le_mul_left _ hloss
      _ = state := Nat.mul_one _⟩

/-- Death condition 3: decaying input.
    If input decays by `decay` bits per cycle, the cumulative decay
    eventually exceeds the initial input. At cycle `initial_input`:
    `initial_input * decay ≥ initial_input`. -/
theorem decaying_input_death
    (initial_input decay : Nat) (hdecay : decay > 0)
    : ∃ n : Nat, n * decay ≥ initial_input := by
  exact ⟨initial_input, by
    calc initial_input * decay
        ≥ initial_input * 1 := Nat.mul_le_mul_left _ hdecay
      _ = initial_input := Nat.mul_one _⟩

/-- Induction on Nat, named for use by `life_persists`.
    Given a base case and an inductive step, the property holds
    for all n. This is standard Nat.rec, not a consequence of the
    death conditions above — it provides the shared inductive
    structure that the death conditions motivate. -/
theorem survival_induction
    (contract_holds : Nat → Prop)
    (base : contract_holds 0)
    (step : ∀ n, contract_holds n → contract_holds (n + 1))
    : ∀ n, contract_holds n := by
  intro n
  induction n with
  | zero => exact base
  | succ k ih => exact step k ih
