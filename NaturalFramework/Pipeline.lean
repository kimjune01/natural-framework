/-!
# Pipeline

The information processing pipeline: five forward stages, one backward pass.

Objects are information states. Morphisms are transformations between them.
Five stages compose forward: Perceive → Cache → Filter → Attend → Remember.
Consolidate runs backward inside the substrate (Remember), reshaping how
each stage processes on the next cycle.

## Main definitions

- `Step` — enumeration of the six pipeline roles
- `Pipeline` — a structure bundling five forward morphisms + backward pass
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

/-- A complete pipeline: five forward morphisms + one backward pass.
    Forward: Perceive → Cache → Filter → Attend → Remember
    Backward: Consolidate (inside the substrate, reshapes parameters) -/
structure Pipeline (I : InterfaceTypes) where
  /-- Forward stages -/
  perceive    : I.raw → I.encoded
  cache       : I.encoded → I.indexed
  filter      : I.indexed → I.selected
  attend      : I.policy → I.selected → I.ranked
  remember    : I.ranked → I.persisted
  /-- Backward pass (inside the substrate, reads from Remember asynchronously) -/
  consolidate : I.policy → I.persisted → I.policy

/-- The forward data path: raw input to persisted output.
    Attend reads policy from the substrate. -/
def Pipeline.forward (p : Pipeline I) (input : I.raw) (policy : I.policy)
    : I.ranked :=
  let encoded := p.perceive input
  let indexed := p.cache encoded
  let selected := p.filter indexed
  p.attend policy selected

/-- One cycle of the pipeline.
    Forward pass produces ranked output. Remember persists it.
    Consolidate reads from Remember (persisted) asynchronously
    and derives a policy update.
    Returns updated policy and persisted state. -/
def Pipeline.cycle (p : Pipeline I) (input : I.raw) (policy : I.policy)
    : I.policy × I.persisted :=
  let ranked := p.forward input policy
  let persisted := p.remember ranked
  let policy' := p.consolidate policy persisted
  (policy', persisted)

/-- The pipeline iterated n times, given a stream of inputs. -/
def Pipeline.iterate (p : Pipeline I) (inputs : Fin n → I.raw)
    (policy₀ : I.policy) : I.policy :=
  match n with
  | 0 => policy₀
  | n + 1 =>
    let rec go (k : Nat) (pol : I.policy) : I.policy :=
      if h : k < n + 1 then
        let (pol', _) := p.cycle (inputs ⟨k, h⟩) pol
        go (k + 1) pol'
      else pol
    go 0 policy₀
