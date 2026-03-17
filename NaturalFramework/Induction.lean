import NaturalFramework.Pipeline
import NaturalFramework.DeathConditions

/-!
# Induction: Life Requires All Six Interfaces at Every Cycle

One axiom, two readings.

## The foundation

`axiom foundation : life_at_zero ∨ attend_is_intentional`

Pick one side. The inductive machinery is identical either way.
The OR is more precise than declaring either side as absolute.

- **Left (empirical)**: life exists at time 0. Observation.
- **Right (teleological)**: the universe's Attend is intentional.
  Selection requires the full pipeline. Life at zero follows.

## The fork

The choice is epistemological, not structural.
Both sides produce `alive_at 0`. Everything after that is shared.

## Axiom chain

Physics axioms → removal tests (Removal.lean) → necessity axioms
(below) → induction theorems.
-/

-- ============================================================
-- Shared predicates
-- ============================================================

/-- The system is viable at cycle k: all six interface contracts hold.
    Budget positive (Perceive), input absorbed (Cache), store bounded
    (Filter), output policy-informed (Attend), policy updated
    (Consolidate), state carried forward (Remember). -/
axiom alive_at : Nat → Prop

/-- Interface s fires at cycle k. Indexed by Step (Pipeline.lean). -/
axiom interface_fires : Step → Nat → Prop

/-- All six interfaces fire at cycle k. -/
def all_six_fire (k : Nat) : Prop :=
  interface_fires .perceive k ∧ interface_fires .cache k ∧
  interface_fires .filter k ∧ interface_fires .attend k ∧
  interface_fires .consolidate k ∧ interface_fires .remember k

/-- What cosmological selection aims toward. -/
axiom Purpose : Type

/-- The universe selects toward this purpose. -/
axiom selects_toward : Purpose → Prop

-- ============================================================
-- Necessity axioms
-- ============================================================
-- Content from removal tests in Removal.lean.
-- Each lifts a static removal result into a temporal frame:
-- alive at k + interface fails → dead at k+1.

/-- Perceive: no injection → dissipation drains budget.
    From: no_perceive_death + dissipation. -/
axiom perceive_necessary (k : Nat) :
  alive_at k → ¬interface_fires .perceive k → ¬alive_at (k + 1)

/-- Cache: no buffer → rate mismatch drops input.
    From: no_cache_death + rate_mismatch. -/
axiom cache_necessary (k : Nat) :
  alive_at k → ¬interface_fires .cache k → ¬alive_at (k + 1)

/-- Filter: no selection → downstream overflow.
    From: no_filter_overflow + landauer + rate_mismatch. -/
axiom filter_necessary (k : Nat) :
  alive_at k → ¬interface_fires .filter k → ¬alive_at (k + 1)

/-- Attend: input-only ranking → history-dependent errors.
    From: no_attend_death + history_matters. -/
axiom attend_necessary (k : Nat) :
  alive_at k → ¬interface_fires .attend k → ¬alive_at (k + 1)

/-- Consolidate: frozen policy → stale on changing env.
    From: no_consolidate_death + landauer (collision). -/
axiom consolidate_necessary (k : Nat) :
  alive_at k → ¬interface_fires .consolidate k → ¬alive_at (k + 1)

/-- Remember: state resets → history-dependent errors.
    From: no_remember_death + history_matters. -/
axiom remember_necessary (k : Nat) :
  alive_at k → ¬interface_fires .remember k → ¬alive_at (k + 1)

/-- All six fire → life continues.
    Content: cycle_preserves_policy (Handshake.lean) closes the
    cross-cycle gap — Consolidate's output at k satisfies Attend's
    policy precondition at k+1. -/
axiom positive_step (k : Nat) :
  alive_at k → all_six_fire k → alive_at (k + 1)

-- ============================================================
-- Dispatch
-- ============================================================

/-- Any single interface failure kills life next cycle. -/
theorem interface_necessary (s : Step) (k : Nat)
    (halive : alive_at k) (hfail : ¬interface_fires s k)
    : ¬alive_at (k + 1) := by
  cases s with
  | perceive => exact perceive_necessary k halive hfail
  | cache => exact cache_necessary k halive hfail
  | filter => exact filter_necessary k halive hfail
  | attend => exact attend_necessary k halive hfail
  | consolidate => exact consolidate_necessary k halive hfail
  | remember => exact remember_necessary k halive hfail

-- ============================================================
-- The foundation
-- ============================================================

/-- Life exists at time 0. Observation. -/
def life_at_zero : Prop := alive_at 0

/-- The universe's Attend is intentional. Purpose. -/
def attend_is_intentional : Prop := ∃ (p : Purpose), selects_toward p

/-- The sixth axiom. At least one holds. -/
axiom foundation : life_at_zero ∨ attend_is_intentional

-- ============================================================
-- Derived base case
-- ============================================================

/-- Intentional selection requires the full pipeline → life at 0. -/
axiom selection_implies_life : attend_is_intentional → alive_at 0

/-- Life at zero — from whichever side of the foundation holds. -/
theorem life_at_zero_holds : alive_at 0 :=
  foundation.elim id selection_implies_life

-- ============================================================
-- Main theorems
-- ============================================================

/-- Life persists when all six interfaces fire every cycle. -/
theorem life_persists
    (all_fire : ∀ k, all_six_fire k)
    : ∀ k, alive_at k :=
  survival_induction alive_at life_at_zero_holds
    (fun k hk => positive_step k hk (all_fire k))

/-- Contrapositive: any interface failure ends life. -/
theorem life_requires_all_six (s : Step) (k : Nat)
    (halive : alive_at k) (hfail : ¬interface_fires s k)
    : ¬alive_at (k + 1) :=
  interface_necessary s k halive hfail

-- ============================================================
-- Axiom verification
-- ============================================================

/- Verify: life_persists depends on `foundation` (the disjunction),
   not on either side independently.
   #print axioms life_persists → foundation, selection_implies_life,
   positive_step, Purpose, selects_toward, alive_at, interface_fires -/
#check @life_persists
#check @life_requires_all_six
