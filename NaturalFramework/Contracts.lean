import NaturalFramework.Pipeline

/-!
# Contracts

Each pipeline step carries a postcondition — a structural guarantee on
its output. A kernel that preserves its contract through composition
belongs in the pipeline. One that doesn't breaks downstream.

All contract definitions quantify over the support of the kernel:
every possible output must satisfy the postcondition.

## The six contracts

| Step        | Type                      | Guarantee                                       |
|-------------|---------------------------|-------------------------------------------------|
| Perceive    | raw → M encoded           | Parseable by next step. Injects new bits.       |
| Cache       | encoded → M indexed       | Retrievable by key.                             |
| Filter      | indexed → M selected      | Strictly smaller.                               |
| Attend      | (policy, selected) → M ranked | Ordered, diverse, bounded.                  |
| Consolidate | (policy, ranked) → M policy'  | Lossy. Includes selection on candidates.    |
| Remember    | policy' → M persisted     | Retrievable on next cycle's Perceive.           |

## Main definitions

- `Contract` — a predicate on morphism outputs
- `ContractPreserving` — all outputs of a kernel satisfy the contract
- `IterationStable` — contract holds under re-application
-/

/-- A contract is a predicate that a morphism's output must satisfy. -/
def Contract (β : Type) := β → Prop

/-- A kernel is contract-preserving if every possible output satisfies
    the contract for every input. Quantifies over support. -/
def ContractPreserving [Monad M] [Support M] (f : Kernel M α β) (contract : Contract β) : Prop :=
  ∀ a : α, ∀ b : β, Support.support (f a) b → contract b

/-- A kernel is iteration-stable if its contract still holds
    when the full pipeline is re-applied. The postcondition survives
    re-application: sort a sorted list — still sorted.
    MMR a diverse slate — still diverse. -/
def IterationStable [Monad M] [Support M] (f : Kernel M α α) (contract : Contract α) : Prop :=
  ∀ a : α, contract a → ∀ b : α, Support.support (f a) b → contract b

/-- Filter contract: output is strictly smaller than input. -/
structure FilterContract (M : Type → Type) [Monad M] [Support M] (α : Type) [SizeOf α] where
  /-- The filter kernel -/
  filter : Kernel M α α
  /-- Every output is strictly smaller -/
  strictly_smaller : ∀ a : α, ∀ b : α, Support.support (filter a) b → sizeOf b < sizeOf a

/-- Attend contract: output is ordered, diverse, and bounded. -/
structure AttendContract (M : Type → Type) [Monad M] [Support M] (α : Type) where
  /-- The ranking kernel -/
  rank : Kernel M α α
  /-- Size measure on outputs -/
  measure : α → Nat
  /-- The capacity bound on output size -/
  bound : Nat
  /-- Every output size is bounded -/
  bounded : ∀ a : α, ∀ b : α, Support.support (rank a) b → measure b ≤ bound
  /-- Winners are dissimilar (diversity) -/
  diverse : α → Prop

/-- Consolidate contract: the operation is lossy and includes
    selection on candidates. The only procedure that writes procedures. -/
structure ConsolidateContract (M : Type → Type) [Monad M] [Support M] (policy ranked : Type) where
  /-- The consolidation kernel -/
  update : policy → Kernel M ranked policy
  /-- Information measure on policy -/
  info : policy → Nat
  /-- Every output is lossy: policy does not grow from ranked input -/
  lossy : ∀ p : policy, ∀ r : ranked, ∀ p' : policy,
    Support.support (update p r) p' → info p' ≤ info p

/-- Remember contract: lossless relative to input.
    No additional loss at this step. Remember is the historically shaped
    substrate — the part of the medium that carries the system's past forward. -/
structure RememberContract (M : Type → Type) [Monad M] [Support M] (α : Type) where
  /-- The persistence kernel -/
  persist : Kernel M α α
  /-- Lossless: for every input, every output equals the input -/
  lossless : ∀ a : α, ∀ b : α, Support.support (persist a) b → b = a

/-- Composition preserves the final contract. Only the last kernel's
    contract matters for the composite's guarantee — the first kernel
    produces intermediates, but the postcondition is checked at the end.

    This is stronger than requiring both contracts: the composite
    preserves `cg` regardless of whether `f` preserves any contract. -/
theorem contract_composition_base [Monad M] [LawfulMonad M] [Support M]
    {f : Kernel M α β} {g : Kernel M β γ}
    {cg : Contract γ}
    (hg : ContractPreserving g cg)
    : ContractPreserving (Kernel.comp f g) cg := by
  intro a c hc
  simp [Kernel.comp] at hc
  rw [Support.support_bind] at hc
  obtain ⟨b, _, hcb⟩ := hc
  exact hg b c hcb

/-- Conjunction: if f preserves Q and R, it preserves both. -/
theorem contractPreserving_post_and [Monad M] [Support M]
    {f : Kernel M α β} {Q R : Contract β}
    (hQ : ContractPreserving f Q) (hR : ContractPreserving f R)
    : ContractPreserving f (fun b => Q b ∧ R b) := by
  intro a b hb
  constructor
  · exact hQ a b hb
  · exact hR a b hb

/-- If f is iteration-stable for c and d, it is iteration-stable for c ∧ d. -/
theorem iterationStable_and [Monad M] [Support M]
    {f : Kernel M α α} {c d : Contract α}
    (hc : IterationStable f c) (hd : IterationStable f d)
    : IterationStable f (fun a => c a ∧ d a) := by
  intro a ha b hb
  obtain ⟨hca, hda⟩ := ha
  constructor
  · exact hc a hca b hb
  · exact hd a hda b hb
