/-!
# Support

Which outputs a monadic computation can produce. This is the
possibilistic (reachability) layer — it tracks which values are
in the support, not their probabilities.

For probability distributions: the support of the measure.
For `Id`: the singleton containing the deterministic output.

## Main definitions

- `Support` — typeclass mapping `M α` to a predicate on `α`
- Instance for `Id` — recovers the deterministic case
-/

-- ============================================================
-- Support: which outputs a computation can produce
-- ============================================================

/-- `Support` tells us which values a monadic computation can produce.
    For probability distributions: the support of the measure.
    For `Id`: the singleton containing the deterministic output. -/
class Support (M : Type → Type) [Monad M] where
  /-- The support predicate: `support m x` means `x` is a possible output of `m`. -/
  support : {α : Type} → M α → α → Prop
  /-- `pure a` supports exactly `a`. -/
  support_pure : ∀ {α : Type} (a x : α), support (pure a) x ↔ x = a
  /-- Bind: `y` is in the support of `m >>= f` iff there exists `x` in the
      support of `m` such that `y` is in the support of `f x`. -/
  support_bind : ∀ {α β : Type} (m : M α) (f : α → M β) (y : β),
    support (bind m f) y ↔ ∃ x, support m x ∧ support (f x) y

-- ============================================================
-- Id instance: the deterministic case
-- ============================================================

/-- `Id` has singleton support: the only possible output is the actual output. -/
instance : Support Id where
  support := fun {α} (m : Id α) (x : α) => x = m
  support_pure := by
    intro α a x
    constructor
    · intro h; exact h
    · intro h; exact h
  support_bind := by
    intro α β m f y
    constructor
    · intro h; exact ⟨m, rfl, h⟩
    · intro ⟨x, hx, hy⟩; rw [hx] at hy; exact hy
