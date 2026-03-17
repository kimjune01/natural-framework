/-!
# Probability Monad

The Kleisli category of a probability monad gives Stoch — the category
whose morphisms are stochastic kernels. This module defines the monad
interface and proves the deterministic case (`M = Id`) satisfies it.

## Main definitions

- `LawfulProbMonad` — a monad with the three monad laws
- `Support` — which outputs a kernel can produce
- Instances for `Id` — recovers the deterministic case
-/

-- ============================================================
-- The probability monad class
-- ============================================================

/-- A lawful probability monad: `Monad` plus the three monad laws.
    Any concrete probability type (Giry, PMF, etc.) that satisfies
    these laws gives a valid Stoch category. -/
class LawfulProbMonad (M : Type → Type) extends Monad M where
  /-- Left identity: `pure a >>= f = f a` -/
  pure_bind : ∀ {α β : Type} (a : α) (f : α → M β),
    bind (pure a) f = f a
  /-- Right identity: `m >>= pure = m` -/
  bind_pure : ∀ {α : Type} (m : M α),
    bind m pure = m
  /-- Associativity: `(m >>= f) >>= g = m >>= (fun x => f x >>= g)` -/
  bind_assoc : ∀ {α β γ : Type} (m : M α) (f : α → M β) (g : β → M γ),
    bind (bind m f) g = bind m (fun x => bind (f x) g)

-- ============================================================
-- Support: which outputs a kernel can produce
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
-- Id instances: the deterministic case
-- ============================================================

/-- `Id` is a lawful probability monad. The deterministic case. -/
instance : LawfulProbMonad Id where
  pure_bind := fun _ _ => rfl
  bind_pure := fun _ => rfl
  bind_assoc := fun _ _ _ => rfl

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
