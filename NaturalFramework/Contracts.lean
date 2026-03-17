/-!
# Contracts

Each pipeline step carries a postcondition — a structural guarantee on
its output. A morphism that preserves its contract through composition
belongs in the pipeline. One that doesn't breaks downstream.

## The six contracts

| Step        | Type                      | Guarantee                                       |
|-------------|---------------------------|-------------------------------------------------|
| Perceive    | raw → encoded             | Parseable by next step. Injects new bits.       |
| Cache       | encoded → indexed         | Retrievable by key.                             |
| Filter      | indexed → selected        | Strictly smaller.                               |
| Attend      | (policy, selected) → ranked | Ordered, diverse, bounded.                    |
| Consolidate | (policy, ranked) → policy'  | Lossy. Includes selection on candidates.      |
| Remember    | policy' → persisted       | Retrievable on next cycle's Perceive.           |

## Main definitions

- `Contract` — a predicate on morphism outputs
- `ContractPreserving` — a morphism satisfies its contract on all inputs
- `IterationStable` — contract holds under re-application
-/

/-- A contract is a predicate that a morphism's output must satisfy. -/
def Contract (β : Type) := β → Prop

/-- A morphism is contract-preserving if its output satisfies the
    contract for every valid input. -/
def ContractPreserving (f : α → β) (contract : Contract β) : Prop :=
  ∀ a : α, contract (f a)

/-- A morphism is iteration-stable if its contract still holds
    when the full pipeline is re-applied. The postcondition survives
    re-application: sort a sorted list — still sorted.
    MMR a diverse slate — still diverse. -/
def IterationStable (f : α → α) (contract : Contract α) : Prop :=
  ∀ a : α, contract a → contract (f a)

/-- Filter contract: output is strictly smaller than input. -/
structure FilterContract (α : Type) [SizeOf α] where
  /-- The filter function -/
  filter : α → α
  /-- Output is strictly smaller -/
  strictly_smaller : ∀ a : α, sizeOf (filter a) < sizeOf a

/-- Attend contract: output is ordered, diverse, and bounded. -/
structure AttendContract (α : Type) where
  /-- The ranking function -/
  rank : α → α
  /-- Size measure on outputs -/
  measure : α → Nat
  /-- Output size is bounded by k -/
  bounded : (k : Nat) → ∀ a : α, measure (rank a) ≤ k
  /-- Winners are dissimilar (diversity) -/
  diverse : α → Prop

/-- Consolidate contract: the operation is lossy and includes
    selection on candidates. The only procedure that writes procedures. -/
structure ConsolidateContract (policy ranked : Type) where
  /-- The consolidation function -/
  update : policy → ranked → policy
  /-- Information measure on policy -/
  info : policy → Nat
  /-- The update is lossy: policy does not grow from ranked input -/
  lossy : ∀ p : policy, ∀ r : ranked, info (update p r) ≤ info p

/-- Remember contract: lossless relative to input.
    No additional loss at this step. Remember is the historically shaped
    substrate — the part of the medium that carries the system's past forward. -/
structure RememberContract (α : Type) where
  /-- The persistence function -/
  persist : α → α
  /-- Lossless: recoverable from output -/
  lossless : Function.Injective persist

/-- The key theorem shape: if all contracts hold, the pipeline composes.
    If any contract breaks, the loop dies. -/
theorem contract_composition_base
    {f : α → β} {g : β → γ}
    {cf : Contract β} {cg : Contract γ}
    (hf : ContractPreserving f cf)
    (hg : ContractPreserving g cg)
    : ContractPreserving (g ∘ f) cg := by
  intro a
  exact hg (f a)
