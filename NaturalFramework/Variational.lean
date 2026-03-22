import NaturalFramework.Handshake

/-!
# Variational Derivations

Two contracts derived as optimality conditions, one packaged from
feasibility constraints.

## Genuine variational derivations

1. **Consolidate**: minimizing output information over a feasible set
   that includes the incumbent policy forces lossiness (info p' ≤ info p).
   The key hypothesis is `self_feasible`: the current policy is always
   an admissible candidate. This is discrete rate-distortion.

2. **Filter**: minimizing output size over a feasible set that contains
   a strictly smaller element forces strict reduction (sizeOf b < sizeOf a).
   The key hypothesis is `strict_witness`: for every input, a feasible
   output exists below it. Minimality plus witness gives the contract.

## Feasibility packaging (not variational)

3. **Attend**: boundedness and diversity follow from the feasibility
   constraint, not from optimization. The proof never uses the
   maximality half of MaximizesOn. Attend's contract is the
   constraint set projected back out. A genuine variational derivation
   of diversity would require cardinality arguments (Finset/Fintype)
   not present in the current possibilistic formalization.

Each section produces a `fromOptimal` (or `fromFeasible`) constructor
that builds the corresponding contract structure, plugging into the
existing handshake and coupling machinery with zero changes downstream.
-/

-- ============================================================
-- Optimality predicates
-- ============================================================

/-- An element minimizes a cost function over a feasible set. -/
def MinimizesOn (cost : α → Nat) (feasible : α → Prop) (x : α) : Prop :=
  feasible x ∧ ∀ y : α, feasible y → cost x ≤ cost y

/-- An element maximizes a score function over a feasible set. -/
def MaximizesOn (score : α → Nat) (feasible : α → Prop) (x : α) : Prop :=
  feasible x ∧ ∀ y : α, feasible y → score y ≤ score x

-- ============================================================
-- Consolidate: lossiness from rate-distortion optimality
-- ============================================================

/-- The consolidation optimization problem.

    The kernel `update` maps (policy, ranked) to a new policy.
    The objective is to minimize `info` of the output policy.
    The feasible set for each (p, r) pair is problem-specific
    (e.g., task-relevant policies).

    `self_feasible` is the discrete rate-distortion content:
    the incumbent policy is always an admissible candidate.
    Any optimal output must therefore cost no more than the
    incumbent — this is the bridge from "optimal over feasible
    set" to "no more informative than input." -/
structure ConsolidateOptimality
    (M : Type → Type) [Monad M] [Support M]
    (policy ranked : Type) where
  /-- The consolidation kernel -/
  update : policy → Kernel M ranked policy
  /-- Information measure on policy -/
  info : InfoMeasure policy
  /-- Feasibility predicate: which output policies are admissible
      given the current policy and ranked input -/
  feasible : policy → ranked → policy → Prop
  /-- The incumbent policy is always feasible -/
  self_feasible : ∀ p : policy, ∀ r : ranked, feasible p r p
  /-- Every output of the kernel is optimal: minimizes info
      over the feasible set -/
  outputs_optimal :
    ∀ p : policy, ∀ r : ranked, ∀ p' : policy,
      Support.support (update p r) p' →
      MinimizesOn info.measure (feasible p r) p'

/-- An optimal consolidation kernel is lossy: output information
    never exceeds input information.

    Proof: the output minimizes info over the feasible set, and the
    incumbent policy is feasible (self_feasible). So info p' ≤ info p. -/
theorem ConsolidateOptimality.optimal_implies_lossy
    {M : Type → Type} [Monad M] [Support M]
    {policy ranked : Type}
    (P : ConsolidateOptimality M policy ranked) :
    ∀ p : policy, ∀ r : ranked, ∀ p' : policy,
      Support.support (P.update p r) p' →
      P.info.measure p' ≤ P.info.measure p := by
  intro p r p' hp'
  obtain ⟨_, hmin⟩ := P.outputs_optimal p r p' hp'
  exact hmin p (P.self_feasible p r)

/-- Build a ConsolidateContract from an optimal consolidation kernel. -/
def ConsolidateContract.fromOptimal
    {M : Type → Type} [Monad M] [Support M]
    {policy ranked : Type}
    (P : ConsolidateOptimality M policy ranked) :
    ConsolidateContract M policy ranked :=
  { update := P.update
    info := P.info.measure
    lossy := P.optimal_implies_lossy }

-- ============================================================
-- Filter: strict reduction from cardinality minimization
-- ============================================================

/-- The filter optimization problem.

    The kernel `filter` maps indexed items to indexed items.
    The objective is to minimize `sizeOf` of the output.
    The feasible set encodes a recall constraint: which outputs
    retain enough for downstream.

    Two hypotheses do the real work:
    - `outputs_optimal`: the kernel picks the smallest feasible output.
    - `strict_witness`: for every input, a feasible output strictly
      smaller than the input exists.

    Minimality gives sizeOf b ≤ sizeOf c for any feasible c.
    The witness gives a feasible c with sizeOf c < sizeOf a.
    Chaining: sizeOf b ≤ sizeOf c < sizeOf a. -/
structure FilterOptimality
    (M : Type → Type) [Monad M] [Support M]
    (α : Type) [SizeOf α] where
  /-- The filter kernel -/
  filter : Kernel M α α
  /-- Feasibility predicate: which outputs satisfy recall -/
  feasible : α → α → Prop
  /-- Every output of the kernel is optimal: minimizes sizeOf
      over the feasible set for that input -/
  outputs_optimal :
    ∀ a : α, ∀ b : α,
      Support.support (filter a) b →
      MinimizesOn (fun c : α => sizeOf c) (feasible a) b
  /-- For every input, a strictly smaller feasible output exists -/
  strict_witness :
    ∀ a : α, ∃ c : α, feasible a c ∧ sizeOf c < sizeOf a

/-- An optimal filter kernel is strictly reducing: every output
    is strictly smaller than the input.

    Proof: optimality gives sizeOf b ≤ sizeOf c for any feasible c.
    strict_witness gives a feasible c with sizeOf c < sizeOf a.
    Chain: sizeOf b ≤ sizeOf c < sizeOf a. -/
theorem FilterOptimality.optimal_implies_strictly_smaller
    {M : Type → Type} [Monad M] [Support M]
    {α : Type} [SizeOf α]
    (P : FilterOptimality M α) :
    ∀ a : α, ∀ b : α,
      Support.support (P.filter a) b →
      sizeOf b < sizeOf a := by
  intro a b hb
  obtain ⟨_, hmin⟩ := P.outputs_optimal a b hb
  obtain ⟨c, hc_feas, hc_lt⟩ := P.strict_witness a
  exact Nat.lt_of_le_of_lt (hmin c hc_feas) hc_lt

/-- Build a FilterContract from an optimal filter kernel. -/
def FilterContract.fromOptimal
    {M : Type → Type} [Monad M] [Support M]
    {α : Type} [SizeOf α]
    (P : FilterOptimality M α) :
    FilterContract M α :=
  { filter := P.filter
    strictly_smaller := P.optimal_implies_strictly_smaller }

-- ============================================================
-- Attend: boundedness from feasibility (not variational)
-- ============================================================

/-- The attend feasibility packaging.

    The kernel `rank` maps indexed items to ranked items.
    Outputs must lie in a feasible set defined by capacity
    (measure ≤ bound) and diversity.

    This is NOT a variational derivation. The proof never uses
    the maximality half of MaximizesOn — both boundedness and
    diversity are just the feasibility constraint projected back
    out. The optimization over `score` exists but does not
    contribute to the contract.

    A genuine variational derivation of diversity would require
    cardinality arguments (Finset/Fintype) to formalize the
    packing argument: replacing a bounded duplicate with a novel
    element increases diversity. That structure is not present
    in the current possibilistic formalization. -/
structure AttendFeasibility
    (M : Type → Type) [Monad M] [Support M]
    (α : Type) where
  /-- The ranking kernel -/
  rank : Kernel M α α
  /-- Size measure on outputs -/
  measure : α → Nat
  /-- The capacity bound -/
  bound : Nat
  /-- Diversity predicate -/
  diverse : α → Prop
  /-- Every output is bounded and diverse -/
  outputs_feasible :
    ∀ a : α, ∀ b : α,
      Support.support (rank a) b →
      measure b ≤ bound ∧ diverse b

/-- Boundedness follows from feasibility. -/
theorem AttendFeasibility.implies_bounded
    {M : Type → Type} [Monad M] [Support M]
    {α : Type}
    (P : AttendFeasibility M α) :
    ∀ a : α, ∀ b : α,
      Support.support (P.rank a) b →
      P.measure b ≤ P.bound := by
  intro a b hb
  exact (P.outputs_feasible a b hb).1

/-- Build an AttendContract from feasibility constraints. -/
def AttendContract.fromFeasible
    {M : Type → Type} [Monad M] [Support M]
    {α : Type}
    (P : AttendFeasibility M α) :
    AttendContract M α :=
  { rank := P.rank
    measure := P.measure
    bound := P.bound
    bounded := P.implies_bounded
    diverse := P.diverse }
