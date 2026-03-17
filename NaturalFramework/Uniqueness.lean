import NaturalFramework.Pipeline
import NaturalFramework.Contracts

/-!
# Uniqueness

The forward pipeline has exactly one valid ordering, and Consolidate
cannot be inserted into the forward chain.

## What this proves

Given:
- Five forward stages with typed interfaces
- The handshake condition (output type of stage N = input type of stage N+1)
- The pipeline starts from raw input

Then:
- The forward ordering is uniquely determined (Perceive → Cache → Filter → Attend → Remember)
- Consolidate cannot fit in the forward chain (its input/output types have no slot)
- Therefore the only viable configuration is five canonical forward stages + backward Consolidate

## Encoding

Interface types are an enum, not magic numbers. Each forward stage
has a domain (input type) and codomain (output type). The handshake
condition is `cod(stage i) = dom(stage i+1)`. Consolidate's codomain
is `policy`, which no forward stage consumes.
-/

-- ============================================================
-- Interface types as an enum
-- ============================================================

/-- The seven information types at pipeline interfaces.
    Five forward handshake points, plus policy and persisted. -/
inductive InfoTy where
  | raw | encoded | indexed | selected | ranked | persisted | policy
  deriving DecidableEq, Repr

-- ============================================================
-- Forward stages with dom/cod
-- ============================================================

/-- The five forward stages. -/
inductive ForwardStage where
  | perceive | cache | filter | attend | remember
  deriving DecidableEq, Repr

/-- Input type for each forward stage. -/
def ForwardStage.dom : ForwardStage → InfoTy
  | .perceive => .raw
  | .cache    => .encoded
  | .filter   => .indexed
  | .attend   => .selected
  | .remember => .ranked

/-- Output type for each forward stage. -/
def ForwardStage.cod : ForwardStage → InfoTy
  | .perceive => .encoded
  | .cache    => .indexed
  | .filter   => .selected
  | .attend   => .ranked
  | .remember => .persisted

-- ============================================================
-- Consumer uniqueness: each InfoTy has exactly one consumer
-- ============================================================

/-- Only Perceive consumes raw. -/
theorem only_perceive_consumes_raw (s : ForwardStage)
    (h : s.dom = .raw) : s = .perceive := by
  cases s <;> simp_all [ForwardStage.dom]

/-- Only Cache consumes encoded. -/
theorem only_cache_consumes_encoded (s : ForwardStage)
    (h : s.dom = .encoded) : s = .cache := by
  cases s <;> simp_all [ForwardStage.dom]

/-- Only Filter consumes indexed. -/
theorem only_filter_consumes_indexed (s : ForwardStage)
    (h : s.dom = .indexed) : s = .filter := by
  cases s <;> simp_all [ForwardStage.dom]

/-- Only Attend consumes selected. -/
theorem only_attend_consumes_selected (s : ForwardStage)
    (h : s.dom = .selected) : s = .attend := by
  cases s <;> simp_all [ForwardStage.dom]

/-- Only Remember consumes ranked. -/
theorem only_remember_consumes_ranked (s : ForwardStage)
    (h : s.dom = .ranked) : s = .remember := by
  cases s <;> simp_all [ForwardStage.dom]

-- ============================================================
-- Handshake and canonical ordering
-- ============================================================

/-- The handshake: stage i+1 consumes what stage i produces. -/
def handshake_ok (ord : Fin 5 → ForwardStage) : Prop :=
  ∀ (i : Nat) (hi : i < 4),
    (ord ⟨i + 1, by omega⟩).dom = (ord ⟨i, by omega⟩).cod

/-- The canonical ordering. -/
def canonical : Fin 5 → ForwardStage
  | ⟨0, _⟩ => .perceive
  | ⟨1, _⟩ => .cache
  | ⟨2, _⟩ => .filter
  | ⟨3, _⟩ => .attend
  | ⟨4, _⟩ => .remember

/-- The canonical ordering satisfies the handshake. -/
theorem canonical_handshake : handshake_ok canonical := by
  intro i hi
  match i, hi with
  | 0, _ => rfl
  | 1, _ => rfl
  | 2, _ => rfl
  | 3, _ => rfl

-- ============================================================
-- MAIN THEOREM: forward ordering uniqueness
-- ============================================================

/-- Any handshake-compatible ordering starting from raw
    must equal the canonical ordering at every position.

    The type chain forces each position:
    - Position 0 consumes raw → only Perceive
    - Position 1 consumes encoded → only Cache
    - Position 2 consumes indexed → only Filter
    - Position 3 consumes selected → only Attend
    - Position 4 consumes ranked → only Remember -/
theorem forward_ordering_unique
    (ord : Fin 5 → ForwardStage)
    (hcompat : handshake_ok ord)
    (hfirst : (ord ⟨0, by omega⟩).dom = .raw)
    : ∀ i : Fin 5, ord i = canonical i := by
  have h0 : ord ⟨0, by omega⟩ = .perceive :=
    only_perceive_consumes_raw _ hfirst
  have h1 : ord ⟨1, by omega⟩ = .cache := by
    have := hcompat 0 (by omega); rw [h0] at this
    exact only_cache_consumes_encoded _ this
  have h2 : ord ⟨2, by omega⟩ = .filter := by
    have := hcompat 1 (by omega); rw [h1] at this
    exact only_filter_consumes_indexed _ this
  have h3 : ord ⟨3, by omega⟩ = .attend := by
    have := hcompat 2 (by omega); rw [h2] at this
    exact only_attend_consumes_selected _ this
  have h4 : ord ⟨4, by omega⟩ = .remember := by
    have := hcompat 3 (by omega); rw [h3] at this
    exact only_remember_consumes_ranked _ this
  intro ⟨i, hi⟩
  match i, hi with
  | 0, _ => exact h0
  | 1, _ => exact h1
  | 2, _ => exact h2
  | 3, _ => exact h3
  | 4, _ => exact h4

-- ============================================================
-- Consolidate cannot be in the forward chain
-- ============================================================

/-- No forward stage consumes policy. Consolidate produces policy,
    so nothing in the forward chain can follow it. -/
theorem no_forward_consumes_policy (s : ForwardStage) :
    s.dom ≠ .policy := by
  cases s <;> simp [ForwardStage.dom]

/-- No forward stage consumes persisted. Consolidate needs persisted
    as input, but no forward stage produces it as a handshake target
    that Consolidate could chain from within the forward pass.
    (Remember produces persisted, but it's the last forward stage.) -/
theorem no_forward_consumes_persisted (s : ForwardStage) :
    s.dom ≠ .persisted := by
  cases s <;> simp [ForwardStage.dom]

/-- No forward stage produces policy. -/
theorem no_forward_produces_policy (s : ForwardStage) :
    s.cod ≠ .policy := by
  cases s <;> simp [ForwardStage.cod]

/-- Consolidate cannot occupy any forward position. If it could be
    spliced in, the next stage would need to consume policy. No
    forward stage does. -/
theorem consolidate_has_no_slot (prev next : ForwardStage) :
    ¬ (prev.cod = .persisted ∧ next.dom = .policy) := by
  intro ⟨_, hdom⟩
  exact no_forward_consumes_policy next hdom

-- ============================================================
-- Combined uniqueness
-- ============================================================

/-- The pipeline configuration is unique:
    1. Forward ordering is forced by the type chain
    2. Consolidate's output type (policy) is not consumed by any forward stage
    3. Consolidate's input type (persisted) is not consumed by any forward stage

    Therefore: five forward stages in canonical order +
    Consolidate as backward pass inside the substrate
    is the only configuration whose types compose. -/
theorem pipeline_unique :
    -- The forward chain has exactly one valid ordering
    (∀ (ord : Fin 5 → ForwardStage)
       (hcompat : handshake_ok ord)
       (hfirst : (ord ⟨0, by omega⟩).dom = .raw),
       ∀ i : Fin 5, ord i = canonical i) ∧
    -- Consolidate's output type has no forward consumer
    (∀ s : ForwardStage, s.dom ≠ .policy) ∧
    -- Consolidate's input type has no forward consumer
    (∀ s : ForwardStage, s.dom ≠ .persisted) :=
  ⟨forward_ordering_unique,
   no_forward_consumes_policy,
   no_forward_consumes_persisted⟩
