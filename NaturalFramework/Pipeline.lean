/-!
# Pipeline

The six-step information processing pipeline as morphisms.

Objects are information states. Morphisms are transformations between them.
The six steps compose sequentially: Perceive → Cache → Filter → Attend →
Consolidate → Remember, with a feedback trace from Remember to Perceive.

## Main definitions

- `Step` — enumeration of the six pipeline steps
- `Pipeline` — a structure bundling six morphisms with compatible types
- `Pipeline.compose` — the full cycle composition
- `Pipeline.iterate` — repeated application (the recursive loop)
-/

/-- The six steps of the pipeline. -/
inductive Step where
  | perceive
  | cache
  | filter
  | attend
  | consolidate
  | remember
  deriving DecidableEq, Repr

/-- Information state: the type flowing between steps.
    Parameterized to allow different representations at each interface. -/
structure InfoState where
  /-- Dimensionality bound -/
  dim : Nat
  /-- The state is nonempty -/
  nonempty : dim > 0

/-- A pipeline morphism: a transformation between information states
    with a declared postcondition. -/
structure Morphism (α β : Type) where
  /-- The transformation function -/
  map : α → β
  /-- The step this morphism implements -/
  step : Step

/-- The six interface types in the pipeline.
    Each handshake point has a distinct type. -/
structure InterfaceTypes where
  raw : Type        -- environment input
  encoded : Type    -- after Perceive
  indexed : Type    -- after Cache
  selected : Type   -- after Filter
  ranked : Type     -- after Attend
  policy : Type     -- after Consolidate
  persisted : Type  -- after Remember (feeds back to Perceive)

/-- A complete pipeline: six morphisms whose types chain. -/
structure Pipeline (I : InterfaceTypes) where
  perceive    : I.raw → I.encoded
  cache       : I.encoded → I.indexed
  filter      : I.indexed → I.selected
  attend      : I.policy → I.selected → I.ranked
  consolidate : I.policy → I.ranked → I.policy
  remember    : I.policy → I.persisted

/-- One cycle of the pipeline.
    Takes environment input and current policy,
    returns updated policy and persisted state. -/
def Pipeline.cycle (p : Pipeline I) (input : I.raw) (policy : I.policy)
    : I.policy × I.persisted :=
  let encoded := p.perceive input
  let indexed := p.cache encoded
  let selected := p.filter indexed
  let ranked := p.attend policy selected
  let policy' := p.consolidate policy ranked
  let persisted := p.remember policy'
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
