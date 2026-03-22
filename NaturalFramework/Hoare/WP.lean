import NaturalFramework.Hoare.Core

/-!
# Hoare Logic Layer — Weakest Precondition

The weakest precondition transformer for monadic kernels.
`wp f Q` is the weakest predicate `P` such that `{P} f {Q}` holds.

## Main definitions

- `wp` — weakest precondition transformer
- `triple_iff_wp` — triples are exactly precondition entailment
- `wp_comp` — wp distributes over sequential composition
- `wp_id` — wp of identity is the postcondition itself
-/

/-- Weakest precondition: the largest set of inputs for which
    every reachable output satisfies `Q`. -/
def wp [Monad M] [Support M] (f : Kernel M α β) (Q : β → Prop) : α → Prop :=
  fun a => ∀ b, Support.support (f a) b → Q b

/-- A Hoare triple holds iff the precondition entails the wp. -/
theorem triple_iff_wp [Monad M] [Support M]
    {P : α → Prop} {f : Kernel M α β} {Q : β → Prop}
    : Triple P f Q ↔ ∀ a, P a → wp f Q a := by
  constructor
  · intro h a hpa b hsup
    exact h a hpa b hsup
  · intro h a hpa b hsup
    exact h a hpa b hsup

/-- wp distributes over Kleisli composition. -/
theorem wp_comp [Monad M] [LawfulMonad M] [Support M]
    (f : Kernel M α β) (k : Kernel M β γ) (Q : γ → Prop)
    : wp (Kernel.comp f k) Q = wp f (wp k Q) := by
  funext a
  apply propext
  constructor
  · intro h b hb c hc
    exact h c (by simp [Kernel.comp]; rw [Support.support_bind]; exact ⟨b, hb, hc⟩)
  · intro h c hc
    simp [Kernel.comp] at hc
    rw [Support.support_bind] at hc
    obtain ⟨b, hb, hcb⟩ := hc
    exact h b hb c hcb

/-- wp of the identity kernel is the postcondition itself. -/
theorem wp_id [Monad M] [Support M] (Q : α → Prop)
    : wp (Kernel.id (M := M)) Q = Q := by
  funext a
  apply propext
  constructor
  · intro h
    exact h a ((Support.support_pure a a).mpr rfl)
  · intro hqa b hsup
    simp [Kernel.id] at hsup
    rw [Support.support_pure] at hsup
    subst hsup
    exact hqa
