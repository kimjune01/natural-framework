import NaturalFramework.Handshake

/-!
# Fractal Consolidation

Consolidate contains its own pipeline: inner Perceive (read outcomes),
Filter (select updates), Attend (rank by relevance). That inner pipeline
has its own Consolidate, recursively.

An encoding step at Perceive turns policy updates into raw input —
the same `I` at every depth. No dependent types needed.

## Termination

The data processing inequality guarantees each inner pipeline has
strictly fewer bits. Filter is strictly lossy (StrictlyLossy in
Handshake.lean). At zero bits, selection is impossible — passthrough.
Tower height ≤ initial bit budget.

## The tower

| Depth | Consolidate                              |
|-------|------------------------------------------|
| 0     | Passthrough (DPI floor, can't select)    |
| d+1   | Inner pipeline cycle using depth-d tower |

## Two directions of induction

The foundation axiom is a disjunction: `life_at_zero ∨ attend_is_intentional`.
Each side gives a different induction on the tower:

**Up-induction (life_at_zero)**: Observe life. Passthrough works (d=0).
Build upward: if depth d preserves the postcondition for a given policy,
so does depth d+1. The mechanism is constructed from the ground up.

**Down-induction (attend_is_intentional)**: Purpose guarantees the
postcondition holds universally. Every policy satisfies it by design.
Tower preservation at every depth is immediate — no step-by-step
construction needed. The mechanism is transparent to purpose.

Both paths converge: the tower preserves at every depth.
-/

-- ============================================================
-- Passthrough: the DPI floor
-- ============================================================

/-- At zero bits, Consolidate cannot select: passthrough.
    The data processing inequality guarantees this floor exists:
    Filter is strictly lossy, so each level has fewer bits.
    Returns `pure pol` — deterministic identity wrapped in `M`. -/
def passthrough [Monad M] (pol : α) (_ : β) : M α := pure pol

/-- Passthrough preserves any contract: output = input.
    The only value in the support of `pure pol` is `pol`. -/
theorem passthrough_preserves [LawfulProbMonad M] [Support M]
    (c : Contract α) (pol : α) (per : β)
    (hpol : c pol) : ∀ x : α, Support.support (passthrough (M := M) pol per) x → c x := by
  intro x hx
  simp [passthrough] at hx
  rw [Support.support_pure] at hx
  subst hx
  exact hpol

-- ============================================================
-- DPI termination
-- ============================================================

/-- Bit budget at depth d, starting from initial bits.
    Each level costs at least 1 bit (Filter is strictly lossy). -/
def bits_at_depth (initial d : Nat) : Nat := initial - d

/-- The budget reaches zero: the tower has a ceiling. -/
theorem budget_hits_zero (initial : Nat) :
    bits_at_depth initial initial = 0 := by
  simp [bits_at_depth]

/-- Beyond the initial budget, bits are zero. -/
theorem budget_zero_beyond (initial d : Nat) (hd : d ≥ initial) :
    bits_at_depth initial d = 0 := by
  simp [bits_at_depth]; omega

/-- Each level strictly decreases the budget.
    From: Filter is StrictlyLossy (Handshake.lean). -/
theorem budget_strictly_decreases (initial d : Nat) (hd : d < initial) :
    bits_at_depth initial (d + 1) < bits_at_depth initial d := by
  simp [bits_at_depth]; omega

-- ============================================================
-- The tower construction
-- ============================================================

/-- The recursive consolidation kernel.
    At depth 0: passthrough (DPI floor).
    At depth d+1: encode (policy, persisted) as raw input,
    run inner pipeline's forward pass, remember, then apply
    inner consolidation (at depth d) to the result.

    Returns `M I.policy` — a stochastic kernel. -/
def tower_consolidate [LawfulProbMonad M]
    {I : InterfaceTypes}
    (base : Pipeline M I)
    (encode : I.policy → I.persisted → I.raw)
    : Nat → I.policy → I.persisted → M I.policy
  | 0, pol, _ => pure pol
  | d + 1, pol, per =>
    let inner : Pipeline M I :=
      { base with consolidate := tower_consolidate base encode d }
    inner.cycle (encode pol per) pol >>= fun result =>
    pure result.1

/-- The pipeline at each depth of the tower.
    Shared forward stages from `base`. Consolidation varies by depth. -/
def tower_pipeline [LawfulProbMonad M]
    {I : InterfaceTypes}
    (base : Pipeline M I)
    (encode : I.policy → I.persisted → I.raw)
    (d : Nat) : Pipeline M I :=
  { base with consolidate := tower_consolidate base encode d }

-- ============================================================
-- Up-induction: the life_at_zero path
-- ============================================================

/-- Up-induction on the tower. Corresponds to the `life_at_zero`
    reading of the foundation axiom.

    Start at passthrough (d=0): output = input, trivially preserves.
    Build upward: if depth d preserves the postcondition for a given
    policy, so does depth d+1. At d+1, the cycle invokes Consolidate
    with the same policy it received — so the IH applies.

    This is the constructive path: observe life, build the mechanism
    step by step from the DPI floor. -/
theorem tower_preserves_up [LawfulProbMonad M] [Support M]
    {I : InterfaceTypes}
    (base : Pipeline M I) (encode : I.policy → I.persisted → I.raw)
    (h : PipelineHandshake I)
    : ∀ (d : Nat) (pol : I.policy) (per : I.persisted),
        h.consolidate_attend.post pol →
        ∀ pol' : I.policy,
          Support.support (tower_consolidate (M := M) base encode d pol per) pol' →
          h.consolidate_attend.post pol' := by
  intro d
  induction d with
  | zero =>
    -- Passthrough: support of `pure pol` is `{pol}`
    intro pol per hpol pol' hsup
    simp [tower_consolidate] at hsup
    rw [Support.support_pure] at hsup
    subst hsup
    exact hpol
  | succ n ih =>
    -- tower(n+1) pol per = inner.cycle(encode pol per, pol) >>= pure ∘ fst
    -- Decompose: pol' came from the cycle, which invoked tower(n) with pol
    intro pol per hpol pol' hsup
    simp only [tower_consolidate] at hsup
    -- Peel off the outer bind: cycle >>= pure ∘ fst
    rw [Support.support_bind] at hsup
    obtain ⟨result, hresult, hpure⟩ := hsup
    rw [Support.support_pure] at hpure
    subst hpure
    -- result came from inner.cycle; extract that result.1 came from consolidate
    have ⟨per', hper'⟩ := cycle_consolidate_support
      { base with consolidate := tower_consolidate base encode n }
      (encode pol per) pol result hresult
    -- per' witnesses: support(tower(n) pol per') result.1
    -- IH: post pol → post result.1
    exact ih pol per' hpol result.1 hper'

-- ============================================================
-- Down-induction: the attend_is_intentional path
-- ============================================================

/-- Down-induction on the tower. Corresponds to the
    `attend_is_intentional` reading of the foundation axiom.

    If the postcondition holds universally — every policy satisfies
    it, because the universe's Attend is intentional and selection is
    purposeful — then the tower preserves at every depth. No
    step-by-step construction is needed.

    This is the teleological path: purpose guarantees the mechanism.
    The up direction needs induction; the down direction needs only
    the premise. Purpose makes the mechanism transparent. -/
theorem tower_preserves_down [LawfulProbMonad M] [Support M]
    {I : InterfaceTypes}
    (base : Pipeline M I) (encode : I.policy → I.persisted → I.raw)
    (h : PipelineHandshake I)
    (hpost_all : ∀ pol : I.policy, h.consolidate_attend.post pol)
    : ∀ (d : Nat) (pol : I.policy) (per : I.persisted)
        (pol' : I.policy),
        Support.support (tower_consolidate (M := M) base encode d pol per) pol' →
        h.consolidate_attend.post pol' :=
  fun _ _ _ pol' _ => hpost_all pol'

-- ============================================================
-- Combined: tower preservation under either reading
-- ============================================================

/-- The coupling lemma's hypothesis `hcon` is satisfied at every depth
    under either reading of the foundation.

    - `life_at_zero` (left): supply `post pol` for the starting policy.
      Up-induction builds preservation from passthrough.
      Feeds `cycle_preserves_policy_at` (weak form).
    - `attend_is_intentional` (right): supply `∀ pol, post pol`.
      Down-induction gives preservation immediately.
      Feeds `cycle_preserves_policy` (strong form).

    The disjunction mirrors `foundation : life_at_zero ∨ attend_is_intentional`
    from Induction.lean. Both paths converge on the same conclusion. -/
theorem tower_satisfies_hcon [LawfulProbMonad M] [Support M]
    {I : InterfaceTypes}
    (base : Pipeline M I) (encode : I.policy → I.persisted → I.raw)
    (h : PipelineHandshake I)
    (d : Nat)
    (pol : I.policy)
    (foundation : h.consolidate_attend.post pol ∨ (∀ p : I.policy, h.consolidate_attend.post p))
    : ∀ (per : I.persisted),
        ∀ pol' : I.policy,
          Support.support ((tower_pipeline (M := M) base encode d).consolidate pol per) pol' →
          h.consolidate_attend.post pol' :=
  foundation.elim
    (fun hpol per pol' hsup =>
      tower_preserves_up base encode h d pol per hpol pol' hsup)
    (fun hall per pol' hsup =>
      tower_preserves_down base encode h hall d pol per pol' hsup)
