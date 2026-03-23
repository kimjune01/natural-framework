import NaturalFramework.Kleisli

/-!
# Hoare Logic — Total Category Packaging

Packages Hoare triples into a total category with weakest-precondition
reindexing. This is organizational, not foundational: the Hoare rules
(triple_comp, triple_consequence, etc.) are proved elsewhere and bundled
here, not derived from the categorical structure.

## What this is

A total category where objects are (type, predicate) pairs and morphisms
are (kernel, proof-it-preserves) pairs. Composition in the total category
corresponds to the already-proved triple_comp. Reindexing = wp.

## What this is NOT

- Not a proved fibration: cartesian universal property not established.
  "Fibration" is aspirational, not a theorem.
- Not Staton's external fibration program (Section 7 of Staton 2025),
  which would put predicates in a separate category with effect algebra
  structure connected by an adjunction.
- Not new mathematics: the meaningful theorems (wp_comp, triple_comp)
  live in Core.lean and WP.lean. This file reorganizes them.

No category-theory library is used.
-/

namespace NaturalFramework

open Function

-- ============================================================
-- Hoare layer
-- ============================================================

/-- `{P} f {Q}` means: for every input satisfying `P`, every possible
output of `f` satisfies `Q`. -/
def Triple [Monad M] [Support M]
    (P : α → Prop) (f : Kernel M α β) (Q : β → Prop) : Prop :=
  ∀ a : α, P a → ∀ b : β, Support.support (f a) b → Q b

/-- Rule of consequence: weaken the precondition, strengthen the postcondition. -/
theorem triple_consequence [Monad M] [Support M]
    {P P' : α → Prop} {Q Q' : β → Prop} {f : Kernel M α β}
    (h : Triple P f Q)
    (hpre : ∀ a, P' a → P a)
    (hpost : ∀ b, Q b → Q' b)
    : Triple P' f Q' := by
  intro a ha b hb
  exact hpost b (h a (hpre a ha) b hb)

/-- Weakest precondition. -/
def wp [Monad M] [Support M] (f : Kernel M α β) (Q : β → Prop) : α → Prop :=
  fun a => ∀ b, Support.support (f a) b → Q b

/-- `Triple` is pointwise entailment into `wp`. -/
theorem triple_iff_wp [Monad M] [Support M]
    {P : α → Prop} {f : Kernel M α β} {Q : β → Prop}
    : Triple P f Q ↔ ∀ a, P a → wp f Q a :=
  Iff.rfl

/-- Reindexing along Kleisli composition is weakest-precondition composition. -/
theorem wp_comp [Monad M] [Support M]
    (f : Kernel M α β) (k : Kernel M β γ) (Q : γ → Prop)
    : wp (Kernel.comp f k) Q = wp f (wp k Q) := by
  funext a
  apply propext
  constructor
  · intro h b hb c hc
    exact h c <| by
      simpa [Kernel.comp] using
        (Support.support_bind (m := f a) (f := k) (y := c)).2 ⟨b, hb, hc⟩
  · intro h c hc
    obtain ⟨b, hb, hk⟩ :=
      (Support.support_bind (m := f a) (f := k) (y := c)).1 <| by
        simpa [Kernel.comp] using hc
    exact h b hb c hk

/-- Weakest precondition of the identity kernel is the predicate itself. -/
theorem wp_id [Monad M] [Support M] (Q : α → Prop)
    : wp (Kernel.id (M := M)) Q = Q := by
  funext a
  apply propext
  constructor
  · intro h
    exact h a <| by
      simpa [Kernel.id] using
        (Support.support_pure (M := M) a a).2 rfl
  · intro ha b hb
    have hba : b = a :=
      (Support.support_pure (M := M) a b).1 <| by
        simpa [Kernel.id] using hb
    simpa [hba] using ha

/-- The COMP rule is derived from `wp_comp`, not taken as an axiom. -/
theorem triple_comp [Monad M] [Support M]
    {P : α → Prop} {Q : β → Prop} {R : γ → Prop}
    {f : Kernel M α β} {k : Kernel M β γ}
    (hf : Triple P f Q)
    (hk : Triple Q k R)
    : Triple P (Kernel.comp f k) R := by
  rw [triple_iff_wp] at hf hk ⊢
  intro a ha
  rw [wp_comp]
  intro b hb
  exact hk b (hf a ha b hb)

/-- Skip rule. -/
theorem triple_skip [Monad M] [Support M]
    {P : α → Prop}
    : Triple P (Kernel.id (M := M)) P := by
  intro a ha b hb
  have hba : b = a :=
    (Support.support_pure (M := M) a b).1 <| by
      simpa [Kernel.id] using hb
  simpa [hba] using ha

-- ============================================================
-- Base category: Kleisli kernels
-- ============================================================

namespace KernelCat

def Hom (M : Type → Type) (α β : Type) : Type := Kernel M α β

def id [Monad M] : Hom M α α := Kernel.id (M := M)

def comp [Monad M] (f : Hom M α β) (g : Hom M β γ) : Hom M α γ :=
  Kernel.comp f g

theorem id_comp [Monad M] [LawfulMonad M] (f : Hom M α β)
    : comp (id (M := M)) f = f :=
  Kernel.id_comp f

theorem comp_id [Monad M] [LawfulMonad M] (f : Hom M α β)
    : comp f (id (M := M)) = f :=
  Kernel.comp_id f

theorem comp_assoc [Monad M] [LawfulMonad M]
    (f : Hom M α β) (g : Hom M β γ) (h : Hom M γ δ)
    : comp (comp f g) h = comp f (comp g h) :=
  Kernel.comp_assoc f g h

end KernelCat

-- ============================================================
-- Total category: types equipped with predicates
-- ============================================================

/-- An object of the total category: a type together with a predicate on it. -/
structure TotalObj where
  α : Type
  pred : α → Prop

/-- A total morphism is a kernel together with a Hoare proof. -/
structure TotalHom (M : Type → Type) [Monad M] [Support M]
    (A B : TotalObj) where
  ker : Kernel M A.α B.α
  cert : Triple A.pred ker B.pred

namespace TotalHom

variable [Monad M] [Support M]

/-- Build a total morphism from a Hoare triple. -/
def ofTriple {P : α → Prop} {Q : β → Prop} {f : Kernel M α β}
    (h : Triple P f Q)
    : TotalHom M ⟨α, P⟩ ⟨β, Q⟩ where
  ker := f
  cert := h

/-- Identity in the total category. -/
def id (A : TotalObj) : TotalHom M A A where
  ker := Kernel.id (M := M)
  cert := triple_skip

/-- Composition in the total category.

This is exactly where the fibration structure shows up: the proof part is
obtained by weakest-precondition composition. -/
def comp {A B C : TotalObj}
    (f : TotalHom M A B) (g : TotalHom M B C)
    : TotalHom M A C where
  ker := Kernel.comp f.ker g.ker
  cert := triple_comp f.cert g.cert

theorem ext {A B : TotalObj} (f g : TotalHom M A B) (h : f.ker = g.ker) : f = g := by
  cases f
  cases g
  cases h
  rfl

theorem id_comp [LawfulMonad M] {A B : TotalObj} (f : TotalHom M A B)
    : comp (id (M := M) A) f = f := by
  apply ext
  exact Kernel.id_comp f.ker

theorem comp_id [LawfulMonad M] {A B : TotalObj} (f : TotalHom M A B)
    : comp f (id (M := M) B) = f := by
  apply ext
  exact Kernel.comp_id f.ker

theorem comp_assoc [LawfulMonad M]
    {A B C D : TotalObj}
    (f : TotalHom M A B) (g : TotalHom M B C) (h : TotalHom M C D)
    : comp (comp f g) h = comp f (comp g h) := by
  apply ext
  exact Kernel.comp_assoc f.ker g.ker h.ker

end TotalHom

-- ============================================================
-- Projection functor
-- ============================================================

/-- The projection from the total category to the base category. -/
structure ProjectionFunctor (M : Type → Type) [Monad M] [Support M] where
  obj : TotalObj → Type
  map : {A B : TotalObj} → TotalHom M A B → Kernel M (obj A) (obj B)
  map_id : ∀ A, map (TotalHom.id (M := M) A) = Kernel.id
  map_comp : ∀ {A B C} (f : TotalHom M A B) (g : TotalHom M B C),
    map (TotalHom.comp f g) = Kernel.comp (map f) (map g)

/-- Forget the predicates, keep the underlying kernel. -/
def proj (M : Type → Type) [Monad M] [Support M] : ProjectionFunctor M where
  obj := fun A => A.α
  map := fun h => h.ker
  map_id := by intro A; rfl
  map_comp := by intro A B C f g; rfl

-- ============================================================
-- Reindexing
-- ============================================================

/-- Reindexing a predicate along a kernel. -/
def reindex [Monad M] [Support M] (f : Kernel M α β) (Q : β → Prop) : α → Prop :=
  wp f Q

/-- Reindexing is exactly weakest precondition. -/
theorem reindex_eq_wp [Monad M] [Support M]
    (f : Kernel M α β) (Q : β → Prop)
    : reindex f Q = wp f Q :=
  rfl

/-- The canonical lift above `f` with codomain predicate `Q`. -/
def cartesianLift [Monad M] [Support M]
    (f : Kernel M α β) (Q : β → Prop)
    : TotalHom M ⟨α, reindex f Q⟩ ⟨β, Q⟩ where
  ker := f
  cert := by
    intro a ha b hb
    exact ha b hb

/-- Reindexing is functorial because `wp` is functorial under Kleisli composition. -/
theorem reindex_comp [Monad M] [Support M]
    (f : Kernel M α β) (k : Kernel M β γ) (Q : γ → Prop)
    : reindex (Kernel.comp f k) Q = reindex f (reindex k Q) :=
  wp_comp f k Q

/-- Identity reindexing is trivial. -/
theorem reindex_id [Monad M] [Support M] (Q : α → Prop)
    : reindex (Kernel.id (M := M)) Q = Q :=
  wp_id Q

-- ============================================================
-- COMP as a property of the fibration
-- ============================================================

/-- The COMP rule is just composition in the total category, projected down. -/
theorem comp_rule_from_fibration [Monad M] [Support M]
    {P : α → Prop} {Q : β → Prop} {R : γ → Prop}
    {f : Kernel M α β} {k : Kernel M β γ}
    (hf : Triple P f Q)
    (hk : Triple Q k R)
    : Triple P (Kernel.comp f k) R :=
  (TotalHom.comp
    (TotalHom.ofTriple (M := M) hf)
    (TotalHom.ofTriple (M := M) hk)).cert

end NaturalFramework
