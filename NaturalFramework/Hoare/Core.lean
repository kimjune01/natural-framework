import NaturalFramework.Handshake

/-!
# Hoare Logic Layer — Core

Hoare triples for monadic kernels. A triple `{P} f {Q}` means:
for every input satisfying `P`, every possible output of `f`
satisfies `Q`. Quantification is over the support — the same
possibilistic layer used throughout NaturalFramework.

## Main definitions

- `Triple` — the Hoare triple for Kleisli arrows
- `triple_consequence` — rule of consequence (weaken pre, strengthen post)
- `triple_comp` — sequential composition rule
- `triple_skip` — skip rule (identity kernel)
-/

/-- Hoare triple for a monadic kernel: every output reachable from
    an input satisfying `P` must satisfy `Q`. -/
def Triple [Monad M] [Support M] (P : α → Prop) (f : Kernel M α β) (Q : β → Prop) : Prop :=
  ∀ a : α, P a → ∀ b : β, Support.support (f a) b → Q b

/-- Rule of consequence: weaken the precondition, strengthen the postcondition. -/
theorem triple_consequence [Monad M] [Support M]
    {P P' : α → Prop} {Q Q' : β → Prop} {f : Kernel M α β}
    (hpre : ∀ a, P' a → P a)
    (hpost : ∀ b, Q b → Q' b)
    (h : Triple P f Q)
    : Triple P' f Q' := by
  intro a hpa' b hsup
  exact hpost b (h a (hpre a hpa') b hsup)

/-- Sequential composition: if `{P} f {R}` and `{R} g {Q}`,
    then `{P} f;g {Q}`. Uses `support_bind` to decompose
    the composite's support, mirroring `contract_composition_base`. -/
theorem triple_comp [Monad M] [LawfulMonad M] [Support M]
    {P : α → Prop} {R : β → Prop} {Q : γ → Prop}
    {f : Kernel M α β} {g : Kernel M β γ}
    (hf : Triple P f R)
    (hg : Triple R g Q)
    : Triple P (Kernel.comp f g) Q := by
  intro a hpa c hc
  simp [Kernel.comp] at hc
  rw [Support.support_bind] at hc
  obtain ⟨b, hb, hcb⟩ := hc
  exact hg b (hf a hpa b hb) c hcb

/-- Skip rule: the identity kernel preserves any predicate.
    Uses `support_pure` to resolve the singleton support. -/
theorem triple_skip [Monad M] [Support M]
    {P : α → Prop}
    : Triple P (Kernel.id (M := M)) P := by
  intro a hpa b hsup
  simp [Kernel.id] at hsup
  rw [Support.support_pure] at hsup
  subst hsup
  exact hpa

/-- AND rule: if f preserves Q and R separately, it preserves both. -/
theorem triple_post_and [Monad M] [Support M]
    {P : α → Prop} {Q R : β → Prop} {f : Kernel M α β}
    (hQ : Triple P f Q) (hR : Triple P f R)
    : Triple P f (fun b => Q b ∧ R b) := by
  intro a ha b hb
  constructor
  · exact hQ a ha b hb
  · exact hR a ha b hb

/-- OR rule: if f satisfies the triple from P₁ and from P₂,
    it satisfies it from their disjunction. -/
theorem triple_pre_or [Monad M] [Support M]
    {P₁ P₂ : α → Prop} {Q : β → Prop} {f : Kernel M α β}
    (h1 : Triple P₁ f Q) (h2 : Triple P₂ f Q)
    : Triple (fun a => P₁ a ∨ P₂ a) f Q := by
  intro a ha b hb
  obtain (h | h) := ha
  · exact h1 a h b hb
  · exact h2 a h b hb
