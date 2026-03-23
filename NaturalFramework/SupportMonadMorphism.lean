import NaturalFramework.Support

/-!
# Support as a Monad Morphism

`Support.support` is a monad morphism from `M` to the reachability monad.
Both laws follow directly from `support_pure` and `support_bind`.

This formalizes the connection to Fritz, Perrone, and Rezagholi (2021):
the support map supp : V ⇒ H is a monad morphism from valuations to
the Hoare hyperspace monad. Our discrete/finite version: support maps
a monadic computation to the set of reachable outputs.
-/

/-- The reachability (powerset) monad: predicates on α. -/
def Reach (α : Type) := α → Prop

/-- Reachability monad instance: pure = singleton, bind = relational composition. -/
instance : Monad Reach where
  pure := fun a x => x = a
  bind := fun s f y => ∃ x, s x ∧ f x y

/-- A monad morphism from M to N: a map that preserves pure and bind. -/
class MonadMorphism (M N : Type → Type) [Monad M] [Monad N] where
  morph : {α : Type} → M α → N α
  morph_pure : ∀ {α : Type} (a : α), morph (pure a : M α) = (pure a : N α)
  morph_bind : ∀ {α β : Type} (m : M α) (f : α → M β),
    morph (m >>= f) = (morph m >>= fun x => morph (f x))

/-- Support is a monad morphism from M to Reach.
    Unit law: support(pure a) = {a}         — from support_pure.
    Bind law: support(m >>= f) = ⋃ₓ∈supp(m) support(f x) — from support_bind. -/
instance supportMonadMorphism (M : Type → Type) [Monad M] [Support M] :
    MonadMorphism M Reach where
  morph := fun m => Support.support m
  morph_pure := by
    intro α a
    funext x
    exact propext (Support.support_pure a x)
  morph_bind := by
    intro α β m f
    funext y
    exact propext (Support.support_bind m f y)
