import NaturalFramework.Support

/-!
# Kleisli Category

Morphisms are monadic kernels: `α → M β`.
When `M = Id`, these are ordinary functions.

## Main definitions

- `Kernel` — the morphism type (Kleisli arrows)
- `Kernel.id` — identity kernel (`pure`)
- `Kernel.comp` — Kleisli composition (`>=>`)
- `Kernel.deterministic` — embedding of pure functions into kernels
- Category laws derived from monad laws
- `deterministic_comp` — embedding preserves composition
-/

-- ============================================================
-- Kernel: the morphism type
-- ============================================================

/-- A monadic kernel from `α` to `β` in monad `M`.
    When `M = Id`, this is `α → β`. -/
def Kernel (M : Type → Type) (α β : Type) := α → M β

-- ============================================================
-- Category structure
-- ============================================================

/-- Identity kernel: wraps the input in `pure`. -/
def Kernel.id [Monad M] : Kernel M α α := fun a => pure a

/-- Kleisli composition: feed output of `f` into `g` via bind. -/
def Kernel.comp [Monad M] (f : Kernel M α β) (g : Kernel M β γ) : Kernel M α γ :=
  fun a => f a >>= g

/-- Embed a deterministic function as a kernel. -/
def Kernel.deterministic [Monad M] (f : α → β) : Kernel M α β :=
  fun a => pure (f a)

-- ============================================================
-- Category laws (derived from monad laws)
-- ============================================================

/-- Left identity: `id >=> f = f`. -/
theorem Kernel.id_comp [Monad M] [LawfulMonad M] (f : Kernel M α β)
    : Kernel.comp Kernel.id f = f := by
  funext a
  simp [Kernel.comp, Kernel.id]

/-- Right identity: `f >=> id = f`. -/
theorem Kernel.comp_id [Monad M] [LawfulMonad M] (f : Kernel M α β)
    : Kernel.comp f Kernel.id = f := by
  funext a
  show f a >>= (fun b => pure b) = f a
  exact bind_pure (f a)

/-- Associativity: `(f >=> g) >=> h = f >=> (g >=> h)`. -/
theorem Kernel.comp_assoc [Monad M] [LawfulMonad M] (f : Kernel M α β)
    (g : Kernel M β γ) (h : Kernel M γ δ)
    : Kernel.comp (Kernel.comp f g) h = Kernel.comp f (Kernel.comp g h) := by
  funext a
  show (f a >>= g) >>= h = f a >>= (fun x => g x >>= h)
  exact bind_assoc (f a) g h

-- ============================================================
-- Deterministic embedding preserves composition
-- ============================================================

/-- Embedding pure functions into kernels preserves composition.
    `deterministic (g ∘ f) = deterministic f >=> deterministic g`. -/
theorem Kernel.deterministic_comp [Monad M] [LawfulMonad M] (f : α → β) (g : β → γ)
    : Kernel.deterministic (M := M) (g ∘ f) = Kernel.comp (Kernel.deterministic f) (Kernel.deterministic g) := by
  funext a
  simp [Kernel.deterministic, Kernel.comp]
