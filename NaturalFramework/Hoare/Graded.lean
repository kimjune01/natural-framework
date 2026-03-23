import NaturalFramework.Hoare.Bridge

/-!
# Hoare Logic Layer — Graded Triples

A graded Hoare triple `{P} f {Q} @ g` combines a behavioral guarantee
(postcondition Q) with a cost bound (grade g).

This is a simplified analog of Gaboardi et al. (ESOP 2021), not a full
implementation of their categorical semantics. Gaboardi uses a preordered
monoid as the grade; we use Nat. The composition law (additive grades)
has the same shape; the generality does not.

## Status: Plausible bridge to Gaboardi

The structural parallel is real: graded triples compose with additive
grades, just as in graded Hoare logic. But `Grade` here is Nat, not a
preordered monoid, and we do not formalize graded Freyd categories.
Closing the bridge requires formalizing Gaboardi's categorical structures.

## Main definitions

- `GradedTriple` — Hoare triple with a Nat cost bound
- `graded_contract_bridge` — ContractPreserving + cost bound → GradedTriple (one direction)
- `graded_comp` — graded triples compose with additive grades
-/

/-- A grade is a cost bound on a morphism. Uses Nat for simplicity;
    Gaboardi's framework uses a preordered monoid. -/
structure Grade where
  /-- The cost bound -/
  cost : Nat
  deriving DecidableEq, Repr

instance : Add Grade where
  add g₁ g₂ := ⟨g₁.cost + g₂.cost⟩

instance : LE Grade where
  le g₁ g₂ := g₁.cost ≤ g₂.cost

/-- A graded Hoare triple: `{P} f {Q} @ g` means
    "for every input satisfying P, every output satisfies Q,
    and the information cost is at most g."

    The cost bound says: output measure + cost ≥ input measure.
    Equivalently: the drop in measure is at most g.
    Stated additively to avoid Nat subtraction issues. -/
def GradedTriple [Monad M] [Support M]
    (P : α → Prop) (f : Kernel M α β) (Q : β → Prop)
    (mα : InfoMeasure α) (mβ : InfoMeasure β) (g : Grade) : Prop :=
  Triple P f Q ∧
  ∀ a : α, P a → ∀ b : β, Support.support (f a) b →
    mα.measure a ≤ mβ.measure b + g.cost

/-- Contract preservation + non-expansion is exactly a graded triple
    with trivial precondition. The grade is the worst-case information loss.

    This is the bridge to Gaboardi et al. (2021): their graded Hoare
    postcondition IS our ContractPreserving + NonExpanding. -/
theorem graded_contract_bridge [Monad M] [Support M]
    {f : Kernel M α β} {Q : Contract β}
    {mα : InfoMeasure α} {mβ : InfoMeasure β} {g : Grade}
    (hcp : ContractPreserving f Q)
    (hne : ∀ a : α, ∀ b : β, Support.support (f a) b →
      mα.measure a ≤ mβ.measure b + g.cost)
    : GradedTriple (fun _ => True) f Q mα mβ g := by
  constructor
  · exact contract_is_triple.mp hcp
  · intro a _ b hsup
    exact hne a b hsup

/-- Extract the behavioral guarantee from a graded triple. -/
theorem graded_triple_to_triple [Monad M] [Support M]
    {P : α → Prop} {f : Kernel M α β} {Q : β → Prop}
    {mα : InfoMeasure α} {mβ : InfoMeasure β} {g : Grade}
    (h : GradedTriple P f Q mα mβ g)
    : Triple P f Q :=
  h.1

/-- Graded triples compose with additive grades.
    If `{P} f {R} @ g₁` and `{R} g {Q} @ g₂`,
    then `{P} f;g {Q} @ (g₁ + g₂)`.

    The behavioral part is the COMP rule.
    The cost part is: total cost ≤ sum of stage costs. -/
theorem graded_comp [Monad M] [LawfulMonad M] [Support M]
    {P : α → Prop} {R : β → Prop} {Q : γ → Prop}
    {f : Kernel M α β} {g : Kernel M β γ}
    {mα : InfoMeasure α} {mβ : InfoMeasure β} {mγ : InfoMeasure γ}
    {g₁ g₂ : Grade}
    (hf : GradedTriple P f R mα mβ g₁)
    (hg : GradedTriple R g Q mβ mγ g₂)
    : GradedTriple P (Kernel.comp f g) Q mα mγ ⟨g₁.cost + g₂.cost⟩ := by
  constructor
  · exact triple_comp hf.1 hg.1
  · intro a hpa c hc
    simp [Kernel.comp] at hc
    rw [Support.support_bind] at hc
    obtain ⟨b, hb, hcb⟩ := hc
    have h1 : mα.measure a ≤ mβ.measure b + g₁.cost := hf.2 a hpa b hb
    have h2 : mβ.measure b ≤ mγ.measure c + g₂.cost := hg.2 b (hf.1 a hpa b hb) c hcb
    -- Chain: mα.a ≤ mβ.b + g₁ ≤ (mγ.c + g₂) + g₁ = mγ.c + (g₁ + g₂)
    calc mα.measure a
        ≤ mβ.measure b + g₁.cost := h1
      _ ≤ (mγ.measure c + g₂.cost) + g₁.cost := Nat.add_le_add_right h2 _
      _ = mγ.measure c + (g₁.cost + g₂.cost) := by omega

/-- The grade of the identity kernel is zero. -/
theorem graded_skip [Monad M] [Support M]
    {P : α → Prop} {mα : InfoMeasure α}
    : GradedTriple P (Kernel.id (M := M)) P mα mα ⟨0⟩ := by
  constructor
  · exact triple_skip
  · intro a _ b hsup
    simp [Kernel.id] at hsup
    rw [Support.support_pure] at hsup
    subst hsup
    omega

/-- Weakening: if a graded triple holds at cost g₁,
    it holds at any larger cost g₂. -/
theorem graded_weaken [Monad M] [Support M]
    {P : α → Prop} {f : Kernel M α β} {Q : β → Prop}
    {mα : InfoMeasure α} {mβ : InfoMeasure β}
    {g₁ g₂ : Grade}
    (h : GradedTriple P f Q mα mβ g₁)
    (hle : g₁.cost ≤ g₂.cost)
    : GradedTriple P f Q mα mβ g₂ := by
  constructor
  · exact h.1
  · intro a hpa b hsup
    have := h.2 a hpa b hsup
    omega
