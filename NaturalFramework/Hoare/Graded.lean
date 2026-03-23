import NaturalFramework.Hoare.Bridge

/-!
# Hoare Logic Layer — Graded Triples

A graded Hoare triple `{P} f {Q} @ g` combines a behavioral guarantee
(postcondition Q) with a cost bound (grade g : G) drawn from a
preordered monoid.

This generalizes the earlier Nat-based `Grade` wrapper to an arbitrary
`PreorderedMonoid`, matching the structural shape of Gaboardi et al.
(ESOP 2021). The composition law (additive grades) and weakening law
(monotone grades) hold for any instance.

## Main definitions

- `PreorderedMonoid` — typeclass: carrier, add, zero, ≤, with associativity,
  unit laws, monotonicity, and a `toNat` extraction for the cost bound
- `instPreorderedMonoidNat` — the canonical Nat instance
- `GradedTriple` — Hoare triple with a grade in G
- `graded_contract_bridge` — ContractPreserving + bound → GradedTriple (one direction)
- `graded_comp` — grades compose via the monoid op
- `graded_skip` — identity kernel has unit grade
- `graded_weaken` — if g₁ ≤ g₂ then a g₁-triple implies a g₂-triple
-/

-- ============================================================
-- PreorderedMonoid typeclass
-- ============================================================

/-- A preordered commutative monoid used as a grade structure.
    `toNat` extracts a numeric cost so that the cost bound can be
    stated additively without Nat subtraction: `mα.measure a ≤ mβ.measure b + toNat g`. -/
class PreorderedMonoid (G : Type) where
  /-- The additive binary operation. -/
  add : G → G → G
  /-- The additive unit. -/
  zero : G
  /-- The preorder on grades. -/
  le : G → G → Prop
  /-- Associativity of addition. -/
  add_assoc : ∀ (a b c : G), add (add a b) c = add a (add b c)
  /-- Left unit law. -/
  zero_add : ∀ (a : G), add zero a = a
  /-- Right unit law. -/
  add_zero : ∀ (a : G), add a zero = a
  /-- Monotonicity: addition on the right is order-preserving. -/
  add_le_add_right : ∀ (a b c : G), le a b → le (add a c) (add b c)
  /-- Numeric extraction for the cost bound statement. -/
  toNat : G → Nat
  /-- The preorder is reflexive. -/
  le_refl : ∀ (a : G), le a a
  /-- The preorder is transitive. -/
  le_trans : ∀ (a b c : G), le a b → le b c → le a c
  /-- `toNat` is order-preserving: smaller grades give smaller cost bounds. -/
  toNat_mono : ∀ (a b : G), le a b → toNat a ≤ toNat b
  /-- `toNat` is additive: the cost of a composed grade is the sum of costs. -/
  toNat_add : ∀ (a b : G), toNat (add a b) = toNat a + toNat b
  /-- `toNat` of the unit is zero. -/
  toNat_zero : toNat zero = 0

-- ============================================================
-- Nat instance
-- ============================================================

/-- The canonical `PreorderedMonoid` instance for `Nat`. -/
instance instPreorderedMonoidNat : PreorderedMonoid Nat where
  add              := Nat.add
  zero             := 0
  le               := (· ≤ ·)
  add_assoc        := Nat.add_assoc
  zero_add         := Nat.zero_add
  add_zero         := Nat.add_zero
  add_le_add_right := fun _ _ c h => Nat.add_le_add_right h c
  toNat            := id
  le_refl          := Nat.le_refl
  le_trans         := fun _ _ _ h1 h2 => Nat.le_trans h1 h2
  toNat_mono       := fun _ _ h => h
  toNat_add        := fun _ _ => rfl
  toNat_zero       := rfl

-- ============================================================
-- GradedTriple
-- ============================================================

/-- A graded Hoare triple: `{P} f {Q} @ g` (with grade `g : G`) means
    - every output reachable from an input satisfying P satisfies Q, and
    - the information drop is bounded by `toNat g`:
      `mα.measure a ≤ mβ.measure b + PreorderedMonoid.toNat g`.

    The cost bound is stated additively to avoid Nat subtraction. -/
def GradedTriple [Monad M] [Support M] {G : Type} [PreorderedMonoid G]
    (P : α → Prop) (f : Kernel M α β) (Q : β → Prop)
    (mα : InfoMeasure α) (mβ : InfoMeasure β) (g : G) : Prop :=
  Triple P f Q ∧
  ∀ a : α, P a → ∀ b : β, Support.support (f a) b →
    mα.measure a ≤ mβ.measure b + PreorderedMonoid.toNat g

-- ============================================================
-- graded_contract_bridge
-- ============================================================

/-- One direction: ContractPreserving + a supplied cost bound → GradedTriple.
    The grade `g` is whatever the caller supplies.
    The converse (that the supplied bound is tight) is not proved here. -/
theorem graded_contract_bridge [Monad M] [Support M] {G : Type} [PreorderedMonoid G]
    {f : Kernel M α β} {Q : Contract β}
    {mα : InfoMeasure α} {mβ : InfoMeasure β} {g : G}
    (hcp : ContractPreserving f Q)
    (hbound : ∀ a : α, ∀ b : β, Support.support (f a) b →
      mα.measure a ≤ mβ.measure b + PreorderedMonoid.toNat g)
    : GradedTriple (fun _ => True) f Q mα mβ g := by
  constructor
  · exact contract_is_triple.mp hcp
  · intro a _ b hsup
    exact hbound a b hsup

-- ============================================================
-- graded_comp
-- ============================================================

/-- Graded triples compose with additive grades.
    If `{P} f {R} @ g₁` and `{R} k {Q} @ g₂`,
    then `{P} f;k {Q} @ (g₁ + g₂)`.

    The behavioral part uses the COMP rule.
    The cost chain is: `mα a ≤ mβ b + toNat g₁ ≤ (mγ c + toNat g₂) + toNat g₁
    = mγ c + toNat (g₁ + g₂)` by `toNat_add`. -/
theorem graded_comp [Monad M] [LawfulMonad M] [Support M] {G : Type} [PreorderedMonoid G]
    {P : α → Prop} {R : β → Prop} {Q : γ → Prop}
    {f : Kernel M α β} {k : Kernel M β γ}
    {mα : InfoMeasure α} {mβ : InfoMeasure β} {mγ : InfoMeasure γ}
    {g₁ g₂ : G}
    (hf : GradedTriple P f R mα mβ g₁)
    (hk : GradedTriple R k Q mβ mγ g₂)
    : GradedTriple P (Kernel.comp f k) Q mα mγ (PreorderedMonoid.add g₁ g₂) := by
  constructor
  · exact triple_comp hf.1 hk.1
  · intro a hpa c hc
    simp [Kernel.comp] at hc
    rw [Support.support_bind] at hc
    obtain ⟨b, hb, hcb⟩ := hc
    have h1 : mα.measure a ≤ mβ.measure b + PreorderedMonoid.toNat g₁ :=
      hf.2 a hpa b hb
    have h2 : mβ.measure b ≤ mγ.measure c + PreorderedMonoid.toNat g₂ :=
      hk.2 b (hf.1 a hpa b hb) c hcb
    rw [PreorderedMonoid.toNat_add]
    calc mα.measure a
        ≤ mβ.measure b + PreorderedMonoid.toNat g₁       := h1
      _ ≤ (mγ.measure c + PreorderedMonoid.toNat g₂)
            + PreorderedMonoid.toNat g₁                  := Nat.add_le_add_right h2 _
      _ = mγ.measure c + (PreorderedMonoid.toNat g₁
            + PreorderedMonoid.toNat g₂)                 := by omega

-- ============================================================
-- graded_skip
-- ============================================================

/-- The identity kernel has unit grade: `{P} id {P} @ zero`.
    The cost bound holds because `support_pure` forces `b = a`,
    so `mα.measure a ≤ mα.measure a + 0` holds by reflexivity.
    `toNat_zero` converts the unit grade to `0`. -/
theorem graded_skip [Monad M] [Support M] {G : Type} [PreorderedMonoid G]
    {P : α → Prop} {mα : InfoMeasure α}
    : GradedTriple P (Kernel.id (M := M)) P mα mα (PreorderedMonoid.zero (G := G)) := by
  constructor
  · exact triple_skip
  · intro a _ b hsup
    simp [Kernel.id] at hsup
    rw [Support.support_pure] at hsup
    subst hsup
    rw [PreorderedMonoid.toNat_zero]
    omega

-- ============================================================
-- graded_weaken
-- ============================================================

/-- Weakening: if a graded triple holds at grade g₁,
    it holds at any larger grade g₂ (with respect to the preorder).
    `toNat_mono` ensures the larger grade gives a larger numeric bound. -/
theorem graded_weaken [Monad M] [Support M] {G : Type} [PreorderedMonoid G]
    {P : α → Prop} {f : Kernel M α β} {Q : β → Prop}
    {mα : InfoMeasure α} {mβ : InfoMeasure β}
    {g₁ g₂ : G}
    (h : GradedTriple P f Q mα mβ g₁)
    (hle : PreorderedMonoid.le g₁ g₂)
    : GradedTriple P f Q mα mβ g₂ := by
  constructor
  · exact h.1
  · intro a hpa b hsup
    have hbound := h.2 a hpa b hsup
    have hmono := PreorderedMonoid.toNat_mono g₁ g₂ hle
    omega

-- ============================================================
-- Derived: extract the behavioral triple
-- ============================================================

/-- Extract the behavioral guarantee from a graded triple. -/
theorem graded_triple_to_triple [Monad M] [Support M] {G : Type} [PreorderedMonoid G]
    {P : α → Prop} {f : Kernel M α β} {Q : β → Prop}
    {mα : InfoMeasure α} {mβ : InfoMeasure β} {g : G}
    (h : GradedTriple P f Q mα mβ g)
    : Triple P f Q :=
  h.1
