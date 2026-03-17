import NaturalFramework.Kleisli

/-!
# Pipeline

The information processing pipeline: five forward stages, one backward pass.

Objects are information states. Morphisms are monadic kernels (`α → M β`).
Five stages compose forward: Perceive → Cache → Filter → Attend → Remember.
Consolidate runs backward inside the substrate (Remember), reshaping how
each stage processes on the next cycle.

When `M = Id`, all kernels reduce to deterministic functions.

## Main definitions

- `Step` — enumeration of the six pipeline roles
- `Pipeline` — a structure bundling five forward kernels + backward pass
- `Pipeline.forward` — the forward data path
- `Pipeline.cycle` — forward pass + backward pass (Consolidate)
- `Pipeline.iterate` — repeated application (the recursive loop)
-/

/-- The six roles of the pipeline.
    Five are forward stages. Consolidate is the backward pass. -/
inductive Step where
  | perceive
  | cache
  | filter
  | attend
  | consolidate
  | remember
  deriving DecidableEq, Repr

/-- The six interface types in the pipeline.
    Five forward handshake points + policy type for the backward pass. -/
structure InterfaceTypes where
  raw : Type        -- environment input
  encoded : Type    -- after Perceive
  indexed : Type    -- after Cache
  selected : Type   -- after Filter
  ranked : Type     -- after Attend
  policy : Type     -- parameterizes Attend; written by Consolidate
  persisted : Type  -- after Remember (feeds back to Perceive)

/-- A complete pipeline: five forward kernels + one backward pass.
    Forward: Perceive → Cache → Filter → Attend → Remember
    Backward: Consolidate (inside the substrate, reshapes parameters)

    All morphisms are monadic kernels in monad `M`.
    When `M = Id`, this recovers the deterministic case. -/
structure Pipeline (M : Type → Type) [Monad M] (I : InterfaceTypes) where
  /-- Forward stages -/
  perceive    : Kernel M I.raw I.encoded
  cache       : Kernel M I.encoded I.indexed
  filter      : Kernel M I.indexed I.selected
  attend      : I.policy → Kernel M I.selected I.ranked
  remember    : Kernel M I.ranked I.persisted
  /-- Backward pass (inside the substrate, reads from Remember asynchronously) -/
  consolidate : I.policy → Kernel M I.persisted I.policy

/-- The forward data path: raw input to ranked output.
    Attend reads policy from the substrate.
    Uses explicit `>>=` for proof tractability. -/
def Pipeline.forward [Monad M] (p : Pipeline M I) (input : I.raw) (policy : I.policy)
    : M I.ranked :=
  p.perceive input >>= fun encoded =>
  p.cache encoded >>= fun indexed =>
  p.filter indexed >>= fun selected =>
  p.attend policy selected

/-- One cycle of the pipeline.
    Forward pass produces ranked output. Remember persists it.
    Consolidate reads from Remember (persisted) asynchronously
    and derives a policy update.
    Returns updated policy and persisted state. -/
def Pipeline.cycle [Monad M] (p : Pipeline M I) (input : I.raw) (policy : I.policy)
    : M (I.policy × I.persisted) :=
  p.forward input policy >>= fun ranked =>
  p.remember ranked >>= fun persisted =>
  p.consolidate policy persisted >>= fun policy' =>
  pure (policy', persisted)

/-- The pipeline iterated n times, given a stream of inputs.
    Each iteration chains via bind. -/
def Pipeline.iterate [Monad M] (p : Pipeline M I) (inputs : Fin n → I.raw)
    (policy₀ : I.policy) : M I.policy :=
  match n with
  | 0 => pure policy₀
  | n + 1 =>
    let rec go (k : Nat) (pol : M I.policy) : M I.policy :=
      if h : k < n + 1 then
        pol >>= fun p' =>
        p.cycle (inputs ⟨k, h⟩) p' >>= fun result =>
        go (k + 1) (pure result.1)
      else pol
    go 0 (pure policy₀)
