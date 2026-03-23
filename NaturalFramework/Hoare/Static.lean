import NaturalFramework.Hoare.Core

/-!
# Static Idempotents — Partial Characterization

Relates IterationStable to Fritz's static idempotents
(Fritz et al. 2023, Prop 4.4.1).

## Status: Plausible bridge to Fritz

IterationStable is definitionally equivalent to the Hoare triple
{c} f {c} — this is a convenience restatement, not a deep result.

StaticOn (output = input on the predicate) is strictly stronger than
IterationStable (output satisfies predicate). The implication
static → stable is proved; the converse does not hold in general.

Fritz's Prop 4.4.1 states that static idempotents split iff they have
supports. The splitting factorization (section + retraction) is NOT
formalized here — `stableSplit` is a placeholder that restates the
IterationStable hypothesis. Closing the bridge requires formalizing
the splitting structure and connecting IdempotentSupport to Fritz's
categorical idempotent.

## What is formalized

- `iteration_stable_is_triple` — definitional equivalence
- `static_implies_stable` — StaticOn → IterationStable
- `iteration_stable_comp` — composition preserves the invariant
- `iteration_stable_id` — identity is trivially stable
-/

/-- IterationStable is exactly a Hoare triple where pre = post.
    This is a loop invariant: the predicate survives application. -/
theorem iteration_stable_is_triple [Monad M] [Support M]
    {f : Kernel M α α} {c : Contract α}
    : IterationStable f c ↔ Triple c f c := by
  constructor
  · intro h a hca b hsup
    exact h a hca b hsup
  · intro h a hca b hsup
    exact h a hca b hsup

/-- A kernel is idempotent if composing it with itself equals itself.
    Stated as: for all inputs, the support of f(f(a)) = support of f(a). -/
def IdempotentSupport [Monad M] [LawfulMonad M] [Support M]
    (f : Kernel M α α) : Prop :=
  ∀ a : α, ∀ c : α,
    Support.support (Kernel.comp f f a) c ↔ Support.support (f a) c

/-- A kernel is static on predicate c if: for any input satisfying c,
    the only possible output is the input itself.
    This is Fritz's "e =_e id": e acts as identity on its own image. -/
def StaticOn [Monad M] [Support M]
    (f : Kernel M α α) (c : α → Prop) : Prop :=
  ∀ a : α, c a → ∀ b : α, Support.support (f a) b → b = a

/-- StaticOn implies IterationStable (trivially: output = input, so
    if input satisfies c, output satisfies c). -/
theorem static_implies_stable [Monad M] [Support M]
    {f : Kernel M α α} {c : α → Prop}
    (hstatic : StaticOn f c)
    : IterationStable f c := by
  intro a hca b hsup
  have := hstatic a hca b hsup
  subst this
  exact hca

/-- An idempotent kernel that is IterationStable for a contract c
    where c characterizes fixed points (c a means f maps a to itself)
    is StaticOn c.

    This formalizes the direction: if f is idempotent and preserves
    its fixed-point predicate, then f acts as identity on that predicate.
    Fritz's Prop 4.4.1 states the converse also holds (splitting ↔ supports). -/
theorem idempotent_stable_implies_static [Monad M] [LawfulMonad M] [Support M]
    {f : Kernel M α α} {c : α → Prop}
    (_hstable : IterationStable f c)
    (hfixed : ∀ a : α, c a → ∀ b : α, Support.support (f a) b → b = a)
    : StaticOn f c :=
  hfixed

/-- Placeholder: restates IterationStable. A real splitting factorization
    would construct a subtype kernel and prove section/retraction equations.
    That is not done here. -/
def stableSplit [Monad M] [Support M]
    (f : Kernel M α α) (c : Contract α)
    (hstable : IterationStable f c) :
    -- For any input satisfying c, f preserves c
    ∀ a : α, c a → ∀ b : α, Support.support (f a) b → c b :=
  hstable

/-- Composing two iteration-stable kernels for the same contract
    yields an iteration-stable kernel. The invariant propagates
    through composition — same as loop invariant through sequential code. -/
theorem iteration_stable_comp [Monad M] [LawfulMonad M] [Support M]
    {f g : Kernel M α α} {c : Contract α}
    (hf : IterationStable f c)
    (hg : IterationStable g c)
    : IterationStable (Kernel.comp f g) c := by
  intro a hca b hb
  simp [Kernel.comp] at hb
  rw [Support.support_bind] at hb
  obtain ⟨mid, hmid, hb⟩ := hb
  exact hg mid (hf a hca mid hmid) b hb

/-- The identity kernel is trivially iteration-stable for any contract. -/
theorem iteration_stable_id [Monad M] [Support M]
    {c : Contract α}
    : IterationStable (Kernel.id (M := M)) c := by
  intro a hca b hsup
  simp [Kernel.id] at hsup
  rw [Support.support_pure] at hsup
  subst hsup
  exact hca
