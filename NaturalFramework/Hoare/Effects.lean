import NaturalFramework.Hoare.Core

/-!
# Effect Algebra — Boolean Embedding

Embeds Boolean contracts (β → Bool) as {0,1}-valued effects.
This is the simplest case of Cho & Jacobs (2015) effectus theory.

## Status: Plausible bridge to Cho-Jacobs

This file shows that Bool-valued contracts correspond to {0,1}-valued
bounded predicates. This is a Bool-to-Prop encoding, not a full effect
algebra formalization. Cho-Jacobs effect algebras have partial addition,
orthocomplement, and unit — none of which are formalized here.
The quantitative case (effects in [0,1]) is not addressed.

`effectPreserving` checks whether outputs are "maximal" (eval b = bound),
which for Boolean effects reduces to ContractPreserving. For non-Boolean
effects this is not a meaningful generalization — it collapses the graded
information. A real bridge requires formalizing the effect algebra axioms.

## Main definitions

- `Effect` — bounded Nat-valued predicate (approximates [0,1]-valued effects)
- `booleanEffect` — embed Bool → {0,1} effect
- `effectPreserving` — "all outputs are maximal" (= ContractPreserving for Boolean case)
- `boolean_effect_bridge` — Bool encoding agreement (definitional)
-/

/-- An effect on type β: a function assigning a value in {0, ..., bound}
    to each element. When bound = 1, this is a Boolean predicate.
    Approximates the [0,1]-valued effects of Cho-Jacobs with Nat. -/
structure Effect (β : Type) where
  /-- The effect function -/
  eval : β → Nat
  /-- The upper bound (1 for Boolean, n for n-valued) -/
  bound : Nat
  /-- Every value is within the bound -/
  bounded : ∀ b : β, eval b ≤ bound

/-- Embed a decidable Boolean contract as a {0,1}-valued effect. -/
def booleanEffect {β : Type} (Q : β → Bool) : Effect β where
  eval := fun b => if Q b then 1 else 0
  bound := 1
  bounded := by
    intro b
    show (if Q b = true then 1 else 0) ≤ 1
    split <;> omega

/-- The top effect: always 1 (always true). -/
def Effect.top (β : Type) : Effect β where
  eval := fun _ => 1
  bound := 1
  bounded := by intro _; omega

/-- The bottom effect: always 0 (always false). -/
def Effect.bot (β : Type) : Effect β where
  eval := fun _ => 0
  bound := 1
  bounded := by intro _; omega

/-- Conjunction of two Boolean effects: min of their values. -/
def Effect.and (e₁ e₂ : Effect β) : Effect β where
  eval := fun b => min (e₁.eval b) (e₂.eval b)
  bound := min e₁.bound e₂.bound
  bounded := by
    intro b
    have h1 := e₁.bounded b
    have h2 := e₂.bounded b
    omega

/-- A kernel preserves an effect if every output's effect value
    is at least the bound (i.e., the effect is "fully satisfied").
    For Boolean effects (bound = 1), this means eval b = 1 for all
    outputs — exactly ContractPreserving. -/
def effectPreserving [Monad M] [Support M]
    (f : Kernel M α β) (e : Effect β) : Prop :=
  ∀ a : α, ∀ b : β, Support.support (f a) b → e.eval b = e.bound

/-- For Boolean effects, effectPreserving is exactly ContractPreserving.
    This is the bridge to Cho-Jacobs: Boolean contracts ARE the {0,1}
    case of effect algebra predicates. -/
theorem boolean_effect_bridge [Monad M] [Support M]
    {f : Kernel M α β} {Q : β → Bool}
    : effectPreserving f (booleanEffect Q) ↔
      ContractPreserving f (fun b => Q b = true) := by
  constructor
  · intro hep a b hsup
    have h := hep a b hsup
    simp [booleanEffect] at h
    by_cases hq : Q b = true
    · exact hq
    · simp [hq] at h
  · intro hcp a b hsup
    simp [booleanEffect]
    have := hcp a b hsup
    simp [this]

/-- Closure under precomposition: if g preserves e, then f;g preserves e
    for any f. This is weaker than binary COMP — it only requires g to
    preserve the effect, not both f and g. -/
theorem effectPreserving_comp [Monad M] [LawfulMonad M] [Support M]
    {f : Kernel M α β} {g : Kernel M β γ}
    {e : Effect γ}
    (hg : effectPreserving g e)
    : effectPreserving (Kernel.comp f g) e := by
  intro a c hc
  simp [Kernel.comp] at hc
  rw [Support.support_bind] at hc
  obtain ⟨b, _, hcb⟩ := hc
  exact hg b c hcb

/-- Point evaluation: an effect applied to a state gives a Nat value.
    For Boolean effects this is 0 or 1 (truth value).
    This is NOT the Born rule — that requires a probabilistic state
    and an expectation pairing, which are not formalized here. -/
def Effect.apply (e : Effect β) (b : β) : Nat := e.eval b

/-- Top evaluates to 1 at every point. -/
theorem Effect.apply_top (b : β) : (Effect.top β).apply b = 1 := by
  simp [Effect.top, Effect.apply]

/-- Applying the bottom effect to any state gives 0. -/
theorem Effect.apply_bot (b : β) : (Effect.bot β).apply b = 0 := by
  simp [Effect.bot, Effect.apply]
