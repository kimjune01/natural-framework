import NaturalFramework.Pipeline
import NaturalFramework.DeathConditions

/-!
# Induction: Life Requires All Six Interfaces at Every Cycle

## The foundation

The base case — `alive 0` — is a field of `SystemModel`, not a
global axiom. The informal argument offers two readings:

- **Left (empirical)**: life exists at time 0. Observation.
- **Right (teleological)**: the universe's Attend is intentional.
  Selection requires the full pipeline. Life at zero follows.

The Lean code does not formalize the disjunction as an axiom.
`SystemModel.base : alive 0` is the base case regardless of which
reading supplies it. The two readings motivate the two induction
directions in Fractal.lean (`tower_preserves_up` and
`tower_preserves_down`), where the disjunction appears explicitly.

## Structure

`SystemModel` bundles the temporal predicates (`alive`, `fires`)
and their relationships. Theorems are parameterized by a model
instance, not by global axioms.

`Purpose` and `selects_toward` are declared as axioms for
completeness but are unused by any theorem. They exist to name
the teleological reading, not to contribute to proofs.
-/

-- ============================================================
-- System model: bundles predicates and necessity conditions
-- ============================================================

/-- All six interfaces fire at cycle k. -/
def all_six_fire (fires : Step → Nat → Prop) (k : Nat) : Prop :=
  fires .perceive k ∧ fires .cache k ∧
  fires .filter k ∧ fires .attend k ∧
  fires .consolidate k ∧ fires .remember k

/-- A system model bundles the temporal predicates (`alive`, `fires`)
    with their relationships (necessity of each interface, sufficiency
    of all six). Replaces 10 axioms with one structure. -/
structure SystemModel where
  /-- The system is viable at cycle k -/
  alive : Nat → Prop
  /-- Interface s fires at cycle k -/
  fires : Step → Nat → Prop
  /-- Base case: life at time 0 -/
  base : alive 0
  /-- Each interface is necessary: failure kills life next cycle -/
  perceive_necessary : ∀ k, alive k → ¬fires .perceive k → ¬alive (k + 1)
  cache_necessary    : ∀ k, alive k → ¬fires .cache k → ¬alive (k + 1)
  filter_necessary   : ∀ k, alive k → ¬fires .filter k → ¬alive (k + 1)
  attend_necessary   : ∀ k, alive k → ¬fires .attend k → ¬alive (k + 1)
  consolidate_necessary : ∀ k, alive k → ¬fires .consolidate k → ¬alive (k + 1)
  remember_necessary : ∀ k, alive k → ¬fires .remember k → ¬alive (k + 1)
  /-- All six fire → life continues -/
  sufficiency : ∀ k, alive k → all_six_fire fires k → alive (k + 1)

-- ============================================================
-- Dispatch
-- ============================================================

/-- Any single interface failure kills life next cycle. -/
theorem interface_necessary (m : SystemModel) (s : Step) (k : Nat)
    (halive : m.alive k) (hfail : ¬m.fires s k)
    : ¬m.alive (k + 1) := by
  cases s with
  | perceive => exact m.perceive_necessary k halive hfail
  | cache => exact m.cache_necessary k halive hfail
  | filter => exact m.filter_necessary k halive hfail
  | attend => exact m.attend_necessary k halive hfail
  | consolidate => exact m.consolidate_necessary k halive hfail
  | remember => exact m.remember_necessary k halive hfail

-- ============================================================
-- The foundation (philosophical axioms — derive the base case)
-- ============================================================

/-- What cosmological selection aims toward. -/
axiom Purpose : Type

/-- The universe selects toward this purpose. -/
axiom selects_toward : Purpose → Prop

/-- Life exists at time 0. An empirical observation. -/
def life_at_zero : Prop := ∃ (alive : Nat → Prop), alive 0

/-- God is real. The universe selects with purpose. -/
def god_is_real : Prop := ∃ (p : Purpose), selects_toward p

/-- The foundation: one of two must hold.

    As with `landauer` and `dissipation`, the Lean axiom is trivially
    satisfiable (`life_at_zero` holds via `fun _ => True`). The content
    is epistemological: the base case for induction comes from either
    observation or purpose. Both readings produce `alive 0` in a
    `SystemModel`. The disjunction is mirrored in `tower_satisfies_hcon`
    (Fractal.lean), where the two branches drive different induction
    directions on the consolidation tower. -/
axiom foundation : life_at_zero ∨ god_is_real

-- ============================================================
-- Main theorems
-- ============================================================

/-- Life persists when all six interfaces fire every cycle. -/
theorem life_persists (m : SystemModel)
    (all_fire : ∀ k, all_six_fire m.fires k)
    : ∀ k, m.alive k :=
  survival_induction m.alive m.base
    (fun k hk => m.sufficiency k hk (all_fire k))

/-- Contrapositive: any interface failure ends life. -/
theorem life_requires_all_six (m : SystemModel) (s : Step) (k : Nat)
    (halive : m.alive k) (hfail : ¬m.fires s k)
    : ¬m.alive (k + 1) :=
  interface_necessary m s k halive hfail

-- ============================================================
-- Axiom verification
-- ============================================================

/- Verify: life_persists depends on SystemModel fields, not global axioms.
   #print axioms life_persists → no axioms beyond propositional logic -/
#check @life_persists
#check @life_requires_all_six
