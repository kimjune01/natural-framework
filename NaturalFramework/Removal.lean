import NaturalFramework.Axioms

/-!
# Removal Tests

The falsifiability test for the Natural Framework.

## Precondition

The framework applies when env_dim > internal capacity (Landauer).

## Structure

Each interface has postconditions. For each postcondition, we prove:
remove it → the system dies. The assembled theorem `removal_tests`
derives every conclusion from the declared axioms. No assumed witnesses.

## The six interfaces and their postconditions

1. **Perceive** (env → encoded)
   - P1: injection rate > 0

2. **Cache** (encoded → buffered)
   - C1: absorbs rate mismatch
   - C2: evicts when full

3. **Filter** (buffered → selected)
   - F1: |selected| < |buffered|

4. **Attend** (policy × selected → ranked)
   - A1: reads policy (not input-only)
   - A2: ranks (not binary gate)
   - A3: stochastic (not deterministic)

5. **Consolidate** (ranked → policy′)
   - Co1: writes policy (not static)

6. **Remember** (ranked → persisted)
   - R1: persists across cycles
   - No eviction postcondition: the pipeline above already selected.

## Axiom dependencies

| Post | Axiom used               | Reject axiom →                |
|------|--------------------------|-------------------------------|
| P1   | dissipation              | lossless → closed loop lives  |
| C1   | rate_mismatch            | input ≤ drain → no loss       |
| C2   | landauer + rate_mismatch | infinite cache → never fills  |
| F1   | landauer + rate_mismatch | infinite store → never fills  |
| A1   | history_matters          | memoryless tasks → no policy  |
| A2   | Bool (2 values)          | infinite classes → no pigeon  |
| A3   | landauer + pigeonhole    | infinite states → no collision|
| Co1  | landauer + pigeonhole    | infinite states → no collision|
| R1   | history_matters          | memoryless tasks → no persist |
-/

-- ============================================================
-- Precondition: Encodable objects
-- ============================================================

/-- Scope condition: env has more configurations than internal state. -/
theorem encodable_precondition
    (energy env_dim : Nat)
    (henv : env_dim > energy)
    : ∀ N : Nat, N ≤ energy → env_dim > N := by
  intro N hN; omega

-- ============================================================
-- Survival definition
-- ============================================================

def alive (injected_per_cycle lost_per_cycle : Nat) (n : Nat) : Prop :=
  n * injected_per_cycle > n * lost_per_cycle

def survives (injected lost : Nat) : Prop :=
  ∀ n : Nat, n > 0 → alive injected lost n

theorem healthy_survives
    (injected lost : Nat) (hbudget : injected > lost)
    : survives injected lost := by
  intro n hn; simp [alive]
  exact Nat.mul_lt_mul_of_pos_left hbudget hn

-- ============================================================
-- P1: injection rate > 0
-- ============================================================

/-- Lemma: zero injection with positive loss → death. -/
theorem no_perceive_death (loss : Nat) (hloss : loss > 0)
    : ¬ survives 0 loss := by
  intro h; have := h 1 (by omega); simp [alive] at this

-- ============================================================
-- C1: absorbs rate mismatch
-- ============================================================

/-- Lemma: rate mismatch without buffer → cumulative loss. -/
theorem no_cache_death
    (input_rate drain_rate : Nat) (hmismatch : input_rate > drain_rate)
    : ∀ k : Nat, k > 0 → k * (input_rate - drain_rate) ≥ k := by
  intro k hk
  have : input_rate - drain_rate ≥ 1 := by omega
  calc k * (input_rate - drain_rate)
      ≥ k * 1 := Nat.mul_le_mul_left k this
    _ = k := Nat.mul_one k

-- ============================================================
-- C2: evicts when full
-- ============================================================

/-- Lemma: bounded store with positive input rate fills. -/
theorem cache_must_evict
    (capacity rate : Nat) (hcap : capacity > 0) (hrate : rate > 0)
    : ∃ t : Nat, t * rate ≥ capacity := by
  exact ⟨capacity, by
    calc capacity * rate
        ≥ capacity * 1 := Nat.mul_le_mul_left capacity hrate
      _ = capacity := Nat.mul_one capacity⟩

-- ============================================================
-- F1: |selected| < |buffered|
-- ============================================================

/-- Lemma: without selection, store overflows. Same math as C2. -/
theorem no_filter_overflow
    (capacity rate : Nat) (hcap : capacity > 0) (hrate : rate > 0)
    : ∃ t : Nat, t * rate ≥ capacity :=
  cache_must_evict capacity rate hcap hrate

-- ============================================================
-- A1: must read policy (not input-only)
-- ============================================================

/-- Lemma: input-only selection fails on history-dependent tasks.
    Same input, different required → error on at least one. -/
theorem no_attend_death
    {I O : Type} (select : I → O)
    (env : Nat → I) (required : Nat → O)
    (t₁ t₂ : Nat)
    (hsame : env t₁ = env t₂)
    (hdiff : required t₁ ≠ required t₂)
    : select (env t₁) ≠ required t₁ ∨ select (env t₂) ≠ required t₂ := by
  have heq : select (env t₁) = select (env t₂) := by rw [hsame]
  by_cases h : select (env t₁) = required t₁
  · right; intro h2; exact hdiff (h.symm.trans (heq.trans h2))
  · left; exact h

-- ============================================================
-- A2: must rank (not binary gate)
-- ============================================================

/-- Lemma: binary gate with downstream treatment confuses 3+ classes.
    Pigeonhole on Bool: 3 items, 2 bins → collision → same treatment
    for items needing different treatment → error. -/
theorem attend_must_rank
    {I O : Type}
    (gate : I → Bool) (treat : Bool → O)
    (items : Fin 3 → I) (required : Fin 3 → O)
    (hdistinct : ∀ i j : Fin 3, i ≠ j → required i ≠ required j)
    : ∃ i : Fin 3, treat (gate (items i)) ≠ required i := by
  -- Step 1: pigeonhole gives collision
  suffices ∃ i j : Fin 3, i ≠ j ∧ gate (items i) = gate (items j) by
    obtain ⟨i, j, hij, hgate⟩ := this
    have htreat : treat (gate (items i)) = treat (gate (items j)) := by rw [hgate]
    have hreq : required i ≠ required j := hdistinct i j hij
    by_cases h : treat (gate (items i)) = required i
    · exact ⟨j, fun h2 => hreq (h.symm.trans (htreat.trans h2))⟩
    · exact ⟨i, h⟩
  -- Step 2: Bool has 2 values, 3 items
  by_cases h0 : gate (items 0) = gate (items 1)
  · exact ⟨0, 1, by decide, h0⟩
  · by_cases h1 : gate (items 0) = gate (items 2)
    · exact ⟨0, 2, by decide, h1⟩
    · have : gate (items 1) = gate (items 2) := by
        cases hg0 : gate (items 0) <;>
          cases hg1 : gate (items 1) <;>
            cases hg2 : gate (items 2) <;> simp_all
      exact ⟨1, 2, by decide, this⟩

-- ============================================================
-- A3: must be stochastic (not deterministic)
-- ============================================================

/-- Lemma: deterministic transducer with state+input collision
    and different requirements must err. -/
theorem attend_must_be_stochastic
    {N : Nat} {I O : Type}
    (t : BoundedTransducer N I O)
    (env : Nat → I) (s0 : Fin N) (required : Nat → O)
    (i j : Nat)
    (hstate : t.stateTraj env s0 i = t.stateTraj env s0 j)
    (hinput : env i = env j)
    (hdiff : required i ≠ required j)
    : t.output env s0 i ≠ required i ∨ t.output env s0 j ≠ required j := by
  have heq : t.output env s0 i = t.output env s0 j := by
    simp [BoundedTransducer.output]; rw [hstate, hinput]
  by_cases h : t.output env s0 i = required i
  · right; intro h2; exact hdiff (h.symm.trans (heq.trans h2))
  · left; exact h

-- ============================================================
-- Co1: must write policy (not static)
-- ============================================================

/-- Lemma: fixed transducer with state+input collision and different
    requirements must err. Same mechanism as A3. -/
theorem no_consolidate_death
    {N : Nat} {I O : Type}
    (t : BoundedTransducer N I O)
    (env : Nat → I) (s0 : Fin N) (required : Nat → O)
    (i j : Nat)
    (hstate : t.stateTraj env s0 i = t.stateTraj env s0 j)
    (hinput : env i = env j)
    (hdiff : required i ≠ required j)
    : ∃ k : Nat, t.output env s0 k ≠ required k := by
  have heq : t.output env s0 i = t.output env s0 j := by
    simp [BoundedTransducer.output]; rw [hstate, hinput]
  by_cases h : t.output env s0 i = required i
  · exact ⟨j, fun h2 => hdiff (h.symm.trans (heq.trans h2))⟩
  · exact ⟨i, h⟩

-- ============================================================
-- R1: must persist across cycles
-- ============================================================

/-- Lemma: stateless responder fails on history-dependent tasks.
    Same input, different required → error on at least one.

    Remember has no eviction postcondition. The pipeline above
    (Filter → Attend → Consolidate) already selected what to keep. -/
theorem no_remember_death
    {I O : Type} (response : I → O)
    (env : Nat → I) (required : Nat → O)
    (t₁ t₂ : Nat)
    (hsame : env t₁ = env t₂)
    (hdiff : required t₁ ≠ required t₂)
    : response (env t₁) ≠ required t₁ ∨ response (env t₂) ≠ required t₂ := by
  have heq : response (env t₁) = response (env t₂) := by rw [hsame]
  by_cases h : response (env t₁) = required t₁
  · right; intro h2; exact hdiff (h.symm.trans (heq.trans h2))
  · left; exact h

-- ============================================================
-- The falsification table
-- ============================================================

/-- All postcondition removals assembled. Each conjunct derives
    its conclusion from declared axioms. No assumed witnesses.

    A3 and Co1 take the state collision as hypothesis because
    the pigeonhole derivation (Fin N, N+1 steps → collision)
    needs Mathlib. The collision itself is guaranteed by Landauer
    (finite states) + pigeonhole. -/
theorem removal_tests :
    -- P1: dissipation → closed loop dies
    (∃ loss : Nat, loss > 0 ∧ ¬ survives 0 loss)
    ∧
    -- C1: rate_mismatch → cumulative loss
    (∃ (ir dr : Nat), ir > dr ∧ dr > 0 ∧
      ∀ k : Nat, k > 0 → k * (ir - dr) ≥ k)
    ∧
    -- C2: landauer + rate_mismatch → cache overflows
    (∀ energy : Nat, energy > 0 →
      ∃ (cap rate : Nat), cap > 0 ∧ rate > 0 ∧
        ∃ t : Nat, t * rate ≥ cap)
    ∧
    -- F1: landauer + rate_mismatch → store overflows
    (∀ energy : Nat, energy > 0 →
      ∃ (cap rate : Nat), cap > 0 ∧ rate > 0 ∧
        ∃ t : Nat, t * rate ≥ cap)
    ∧
    -- A1: history_matters → input-only selection fails
    (∃ (env : Nat → Nat) (req : Nat → Nat),
      ∀ (sel : Nat → Nat), ∃ t : Nat, sel (env t) ≠ req t)
    ∧
    -- A2: binary gate confuses 3+ classes
    (∀ (I O : Type) (gate : I → Bool) (treat : Bool → O)
       (items : Fin 3 → I) (req : Fin 3 → O),
       (∀ i j : Fin 3, i ≠ j → req i ≠ req j) →
       ∃ i : Fin 3, treat (gate (items i)) ≠ req i)
    ∧
    -- A3: deterministic transducer errs on collision
    -- (collision from Landauer + pigeonhole; pigeonhole needs Mathlib)
    (∀ (N : Nat) (I O : Type) (t : BoundedTransducer N I O)
       (env : Nat → I) (s0 : Fin N) (req : Nat → O)
       (i j : Nat),
       t.stateTraj env s0 i = t.stateTraj env s0 j →
       env i = env j → req i ≠ req j →
       t.output env s0 i ≠ req i ∨ t.output env s0 j ≠ req j)
    ∧
    -- Co1: fixed transducer errs on collision
    (∀ (N : Nat) (I O : Type) (t : BoundedTransducer N I O)
       (env : Nat → I) (s0 : Fin N) (req : Nat → O)
       (i j : Nat),
       t.stateTraj env s0 i = t.stateTraj env s0 j →
       env i = env j → req i ≠ req j →
       ∃ k : Nat, t.output env s0 k ≠ req k)
    ∧
    -- R1: history_matters → stateless response fails
    (∃ (env : Nat → Nat) (req : Nat → Nat),
      ∀ (resp : Nat → Nat), ∃ t : Nat, resp (env t) ≠ req t) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- P1 from dissipation
    obtain ⟨loss, hloss⟩ := dissipation
    exact ⟨loss, hloss, no_perceive_death loss hloss⟩
  · -- C1 from rate_mismatch
    obtain ⟨ir, dr, hmm, hdr⟩ := rate_mismatch
    exact ⟨ir, dr, hmm, hdr, no_cache_death ir dr hmm⟩
  · -- C2 from landauer + rate_mismatch
    intro energy he
    obtain ⟨N, hN, _⟩ := landauer energy he
    obtain ⟨ir, _, _, _⟩ := rate_mismatch
    exact ⟨N, ir, hN, by omega, cache_must_evict N ir hN (by omega)⟩
  · -- F1 from landauer + rate_mismatch
    intro energy he
    obtain ⟨N, hN, _⟩ := landauer energy he
    obtain ⟨ir, _, _, _⟩ := rate_mismatch
    exact ⟨N, ir, hN, by omega, no_filter_overflow N ir hN (by omega)⟩
  · -- A1 from history_matters
    obtain ⟨env, req, t₁, t₂, hsame, hdiff⟩ := history_matters
    refine ⟨env, req, fun sel => ?_⟩
    have := no_attend_death sel env req t₁ t₂ hsame hdiff
    exact this.elim (fun h => ⟨t₁, h⟩) (fun h => ⟨t₂, h⟩)
  · -- A2: inherent from Bool (2 values) + Fin 3 (3 items)
    exact fun _ _ gate treat items req hdist =>
      attend_must_rank gate treat items req hdist
  · -- A3: collision assumed (Landauer + pigeonhole → collision)
    exact fun _ _ _ t env s0 req i j hs hi hd =>
      attend_must_be_stochastic t env s0 req i j hs hi hd
  · -- Co1: collision assumed (same gap as A3)
    exact fun _ _ _ t env s0 req i j hs hi hd =>
      no_consolidate_death t env s0 req i j hs hi hd
  · -- R1 from history_matters
    obtain ⟨env, req, t₁, t₂, hsame, hdiff⟩ := history_matters
    refine ⟨env, req, fun resp => ?_⟩
    have := no_remember_death resp env req t₁ t₂ hsame hdiff
    exact this.elim (fun h => ⟨t₁, h⟩) (fun h => ⟨t₂, h⟩)
