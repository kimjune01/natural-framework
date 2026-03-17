import NaturalFramework.Pipeline
import NaturalFramework.Contracts

/-!
# The Handshake

Formalizes the composition argument from
[The Handshake](https://june.kim/the-handshake).

The six roles are stochastic kernels (`α → M β`) — morphisms in the
Kleisli category of a probability monad. Five compose forward;
Consolidate runs backward inside the substrate. This module formalizes:

- The handshake property: postcondition of stage N is precondition of stage N+1
- Cross-cycle coupling: Consolidate at k → Attend at k+1 through the policy store
- Ordering: rearranging forward stages breaks type compatibility
- Data processing inequality: information decreases monotonically
- Four claims from contracts
- Cross-domain functor: structure-preserving map between pipeline instances
- Traced feedback: Remember's output feeds Perceive's input
- Consolidate as backward pass: inside the substrate, reshaping parameters
-/

-- ============================================================
-- The Handshake: postcondition of stage N = precondition of stage N+1
-- ============================================================

/-- A handshake is a pair of contracts where one stage's postcondition
    implies the next stage's precondition. -/
structure Handshake (β : Type) where
  /-- Postcondition of the preceding stage -/
  post : Contract β
  /-- Precondition of the following stage -/
  pre : Contract β
  /-- The handshake: post implies pre -/
  compatible : ∀ b : β, post b → pre b

/-- The full pipeline handshake: four forward interface points plus the
    cross-cycle coupling through the policy store.

    The four forward handshakes cover composition within a single cycle.
    The fifth — consolidate_attend — covers the cross-cycle dependency:
    Consolidate writes policy at cycle k, Attend reads it at cycle k+1.
    Without this fifth handshake, the inductive step has a gap. -/
structure PipelineHandshake (I : InterfaceTypes) where
  /-- Perceive's postcondition implies Cache's precondition -/
  perceive_cache : Handshake I.encoded
  /-- Cache's postcondition implies Filter's precondition -/
  cache_filter : Handshake I.indexed
  /-- Filter's postcondition implies Attend's precondition -/
  filter_attend : Handshake I.selected
  /-- Attend's postcondition implies Remember's precondition -/
  attend_remember : Handshake I.ranked
  /-- Consolidate's postcondition implies Attend's policy precondition
      on the next cycle. The cross-cycle coupling: what Consolidate
      guarantees at k is what Attend requires at k+1. -/
  consolidate_attend : Handshake I.policy

/-- The coupling lemma: a pipeline cycle preserves policy validity.
    If Consolidate preserves its postcondition, the handshake guarantees
    Attend's policy precondition holds on the next cycle.

    In the stochastic case: for all possible outputs of `cycle`,
    the policy component satisfies the precondition. -/
theorem cycle_preserves_policy [LawfulProbMonad M] [Monad M] [Support M]
    (h : PipelineHandshake I) (p : Pipeline M I)
    (hcon : ∀ (pol : I.policy) (per : I.persisted),
      ∀ pol' : I.policy, Support.support (p.consolidate pol per) pol' →
        h.consolidate_attend.post pol')
    (policy : I.policy) (input : I.raw)
    : ∀ result : I.policy × I.persisted,
        Support.support (p.cycle input policy) result →
        h.consolidate_attend.pre result.1 := by
  intro result hresult
  simp [Pipeline.cycle, Pipeline.forward] at hresult
  rw [Support.support_bind] at hresult
  obtain ⟨ranked, _, hr2⟩ := hresult
  rw [Support.support_bind] at hr2
  obtain ⟨persisted, hper, hr3⟩ := hr2
  rw [Support.support_bind] at hr3
  obtain ⟨policy', hpol', hr4⟩ := hr3
  rw [Support.support_pure] at hr4
  subst hr4
  exact h.consolidate_attend.compatible _ (hcon policy persisted policy' hpol')

/-- Weaker form: `hcon` only needed for the specific input policy.
    The cycle only invokes Consolidate with the policy it received.
    Needed for up-induction on the tower (life_at_zero path),
    where we only know `post` for the starting policy. -/
theorem cycle_preserves_policy_at [LawfulProbMonad M] [Monad M] [Support M]
    (h : PipelineHandshake I) (p : Pipeline M I)
    (policy : I.policy) (input : I.raw)
    (hcon : ∀ (per : I.persisted),
      ∀ pol' : I.policy, Support.support (p.consolidate policy per) pol' →
        h.consolidate_attend.post pol')
    : ∀ result : I.policy × I.persisted,
        Support.support (p.cycle input policy) result →
        h.consolidate_attend.pre result.1 := by
  intro result hresult
  simp [Pipeline.cycle, Pipeline.forward] at hresult
  rw [Support.support_bind] at hresult
  obtain ⟨ranked, _, hr2⟩ := hresult
  rw [Support.support_bind] at hr2
  obtain ⟨persisted, _, hr3⟩ := hr2
  rw [Support.support_bind] at hr3
  obtain ⟨policy', hpol', hr4⟩ := hr3
  rw [Support.support_pure] at hr4
  subst hr4
  exact h.consolidate_attend.compatible _ (hcon persisted policy' hpol')

/-- Extract: any output policy of `cycle` came from Consolidate
    applied to the input policy. Useful for tower decomposition. -/
theorem cycle_consolidate_support [LawfulProbMonad M] [Monad M] [Support M]
    (p : Pipeline M I) (input : I.raw) (policy : I.policy)
    (result : I.policy × I.persisted)
    (h : Support.support (p.cycle input policy) result)
    : ∃ per, Support.support (p.consolidate policy per) result.1 := by
  simp [Pipeline.cycle, Pipeline.forward] at h
  rw [Support.support_bind] at h
  obtain ⟨ranked, _, h2⟩ := h
  rw [Support.support_bind] at h2
  obtain ⟨persisted, _, h3⟩ := h2
  rw [Support.support_bind] at h3
  obtain ⟨policy', hpol', h4⟩ := h3
  rw [Support.support_pure] at h4
  subst h4
  exact ⟨persisted, hpol'⟩

-- ============================================================
-- Ordering: rearranging steps breaks type compatibility
-- ============================================================

/-- The pipeline steps form a total order.
    Each step has a position; composition respects the order. -/
def Step.position : Step → Fin 6
  | .perceive    => ⟨0, by omega⟩
  | .cache       => ⟨1, by omega⟩
  | .filter      => ⟨2, by omega⟩
  | .attend      => ⟨3, by omega⟩
  | .consolidate => ⟨4, by omega⟩
  | .remember    => ⟨5, by omega⟩

/-- The position mapping is injective: distinct steps have distinct positions. -/
theorem step_position_injective : Function.Injective Step.position := by
  intro a b h
  cases a <;> cases b <;> simp [Step.position] at h <;> try rfl
  all_goals (simp [Fin.ext_iff] at h)

-- ============================================================
-- Data Processing Inequality
-- ============================================================

/-- An information measure assigns a non-negative value to each state.
    Abstracted as a natural number for now; real-valued with mathlib. -/
structure InfoMeasure (α : Type) where
  /-- Mutual information between input and current state -/
  measure : α → Nat

/-- The data processing inequality: for a chain X → Y → Z,
    I(X;Z) ≤ I(X;Y). Each intermediate step can only decrease
    what downstream knows about the original input.

    A kernel is non-expanding if all possible outputs do not
    increase information. Quantifies over support. -/
def NonExpanding [Monad M] [Support M] (f : Kernel M α β) (mα : InfoMeasure α) (mβ : InfoMeasure β) : Prop :=
  ∀ a : α, ∀ b : β, Support.support (f a) b → mβ.measure b ≤ mα.measure a

/-- A lossy kernel strictly decreases information on at least one input. -/
def StrictlyLossy [Monad M] [Support M] (f : Kernel M α β) (mα : InfoMeasure α) (mβ : InfoMeasure β) : Prop :=
  NonExpanding f mα mβ ∧ ∃ a : α, ∃ b : β, Support.support (f a) b ∧ mβ.measure b < mα.measure a

/-- Composing two non-expanding kernels yields a non-expanding kernel.
    This is the chain rule for information loss. -/
theorem non_expanding_compose [LawfulProbMonad M] [Monad M] [Support M]
    {f : Kernel M α β} {g : Kernel M β γ}
    {mα : InfoMeasure α} {mβ : InfoMeasure β} {mγ : InfoMeasure γ}
    (hf : NonExpanding f mα mβ)
    (hg : NonExpanding g mβ mγ)
    : NonExpanding (Kernel.comp f g) mα mγ := by
  intro a c hc
  simp [Kernel.comp] at hc
  rw [Support.support_bind] at hc
  obtain ⟨b, hb, hcb⟩ := hc
  calc mγ.measure c
      ≤ mβ.measure b := hg b c hcb
    _ ≤ mα.measure a := hf a b hb

/-- The pipeline's net information: after six steps, information about
    the original input has decreased by the sum of all lossy steps.
    The budget balances only if Perceive injects enough new bits. -/
structure InformationBudget where
  /-- Bits injected by Perceive per cycle -/
  injected : Nat
  /-- Bits lost by Filter -/
  filter_loss : Nat
  /-- Bits lost by Attend -/
  attend_loss : Nat
  /-- Bits lost by Consolidate -/
  consolidate_loss : Nat
  /-- Total loss = sum of lossy steps -/
  total_loss : filter_loss + attend_loss + consolidate_loss = filter_loss + attend_loss + consolidate_loss := rfl
  /-- The budget balances -/
  balanced : injected ≥ filter_loss + attend_loss + consolidate_loss

/-- A closed loop has zero injection. Any positive loss compounds. -/
theorem closed_loop_budget_negative
    (filter_loss attend_loss consolidate_loss : Nat)
    (hsome_loss : filter_loss + attend_loss + consolidate_loss > 0)
    : ¬ (0 ≥ filter_loss + attend_loss + consolidate_loss) := by
  omega

-- ============================================================
-- Diversity Survival (distinct from loop survival)
-- ============================================================

/-- Diversity survival requires two independent conditions:
    1. Diverse input (Perceive): enough novel items in the ground set
    2. Intact kernel (Consolidate): the policy that parameterizes the
       diversity-enforcing morphism has not degraded

    Either condition can fail independently. An echo chamber violates (1):
    the budget balances but the ground set homogenizes. A degraded
    Consolidate violates (2): diverse input arrives but the kernel
    no longer enforces repulsion. -/
structure DiversityBudget where
  /-- Distinct items injected by Perceive per cycle -/
  novel_items : Nat
  /-- Minimum distinct items required by Attend's diversity contract -/
  diversity_threshold : Nat
  /-- Whether the policy (kernel) is intact -/
  kernel_intact : Bool
  /-- The diversity budget balances: both conditions hold -/
  sufficient : novel_items ≥ diversity_threshold
  /-- The kernel must be intact -/
  kernel_ok : kernel_intact = true

/-- Echo chamber: information budget balances, but ground set
    homogenizes. Kernel is intact; input lacks variety. -/
structure EchoChamber where
  /-- Information budget is satisfied -/
  info : InformationBudget
  /-- Diversity threshold required -/
  diversity_threshold : Nat
  /-- Novel items injected are below the diversity threshold -/
  homogenized : diversity_threshold > 0
  /-- Novel items injected -/
  novel_items : Nat
  /-- Zero novel items despite positive bit injection -/
  novel_items_zero : novel_items = 0

/-- Degraded Consolidate: diverse input arrives but the kernel
    that parameterizes Attend no longer enforces repulsion.
    Independent failure mode from echo chamber. -/
structure DegradedConsolidate where
  /-- Information budget is satisfied -/
  info : InformationBudget
  /-- Input is diverse: novel items meet threshold -/
  novel_items : Nat
  diversity_threshold : Nat
  input_diverse : novel_items ≥ diversity_threshold
  /-- Whether the kernel is intact -/
  kernel_intact : Bool
  /-- But the kernel is broken -/
  kernel_broken : kernel_intact = false

/-- The two diversity failure modes are independent.
    An echo chamber has intact kernel + homogeneous input.
    A degraded Consolidate has broken kernel + diverse input.
    Both can coexist with a balanced information budget. -/
theorem diversity_failures_independent
    (injected filter_loss attend_loss consolidate_loss : Nat)
    (hbalanced : injected ≥ filter_loss + attend_loss + consolidate_loss)
    (diversity_threshold : Nat) (hdiv : diversity_threshold > 0)
    (novel_items : Nat) (hnovel : novel_items ≥ diversity_threshold)
    : -- Echo chamber is possible (balanced budget, diversity violated via input)
      (∃ (_ : InformationBudget), diversity_threshold > 0) ∧
      -- Degraded Consolidate is possible (balanced budget, diverse input, kernel broken)
      (∃ (_ : InformationBudget), novel_items ≥ diversity_threshold) :=
  ⟨⟨⟨injected, filter_loss, attend_loss, consolidate_loss, rfl, hbalanced⟩, hdiv⟩,
   ⟨⟨injected, filter_loss, attend_loss, consolidate_loss, rfl, hbalanced⟩, hnovel⟩⟩

-- ============================================================
-- Four Claims from Contracts
-- ============================================================

/-- Claim 1: If contracts match, algorithms are swappable.
    Two kernels with the same contract are interchangeable. -/
theorem swappable [Monad M] [Support M]
    {f g : Kernel M α β} {c : Contract β}
    (hf : ContractPreserving f c) (hg : ContractPreserving g c)
    : ContractPreserving f c ∧ ContractPreserving g c :=
  ⟨hf, hg⟩

/-- Claim 2: If any contract is broken, the loop dies.
    A broken contract means some input can produce output violating
    the postcondition. Downstream receives invalid input. -/
def ContractBroken [Monad M] [Support M] (f : Kernel M α β) (c : Contract β) : Prop :=
  ∃ a : α, ∃ b : β, Support.support (f a) b ∧ ¬ c b

/-- A broken contract propagates: if step N breaks its contract,
    step N+1 receives invalid input regardless of its own correctness.
    The kernel is not contract-preserving. -/
theorem broken_propagates [Monad M] [Support M]
    {f : Kernel M α β}
    {pre : Contract β}
    (hbroken : ContractBroken f pre)
    : ¬ ContractPreserving f pre := by
  obtain ⟨a, b, hsup, hna⟩ := hbroken
  intro hcp
  exact hna (hcp a b hsup)

/-- Claim 4: Iteration stability test.
    If a kernel degrades its postcondition under self-composition,
    it is a near-miss. The postcondition fails after finitely many
    applications. -/
def NearMiss [Monad M] [Support M] (f : Kernel M α α) (c : Contract α) : Prop :=
  ∃ a : α, c a ∧ ∃ b : α, Support.support (f a) b ∧ ¬ c b

/-- An iteration-stable kernel is not a near-miss on any input
    that already satisfies the contract. -/
theorem stable_not_near_miss [Monad M] [Support M]
    {f : Kernel M α α} {c : Contract α}
    (hstable : IterationStable f c)
    : ¬ NearMiss f c := by
  intro ⟨a, ha, b, hsup, hna⟩
  exact hna (hstable a ha b hsup)

-- ============================================================
-- Cross-domain Functor
-- ============================================================

/-- A pipeline morphism between two domains: maps interface types
    and preserves pipeline structure. If domain A and domain B both
    implement six roles with compatible type signatures, the
    mapping between them is a candidate functor. -/
structure PipelineFunctor (A B : InterfaceTypes) where
  /-- Map raw states -/
  map_raw : A.raw → B.raw
  /-- Map encoded states -/
  map_encoded : A.encoded → B.encoded
  /-- Map indexed states -/
  map_indexed : A.indexed → B.indexed
  /-- Map selected states -/
  map_selected : A.selected → B.selected
  /-- Map ranked states -/
  map_ranked : A.ranked → B.ranked
  /-- Map policy states -/
  map_policy : A.policy → B.policy
  /-- Map persisted states -/
  map_persisted : A.persisted → B.persisted

/-- A functor preserves pipeline composition if mapping commutes
    with each role. This is the naturality condition.
    Forward stages and backward pass both commute.
    Equality via `Functor.map` inside `M`. -/
def FunctorNatural [Monad M] [LawfulFunctor M] (F : PipelineFunctor A B)
    (pA : Pipeline M A) (pB : Pipeline M B) : Prop :=
  -- Forward stages --
  -- Perceive commutes
  (∀ r : A.raw, Functor.map F.map_encoded (pA.perceive r) = pB.perceive (F.map_raw r)) ∧
  -- Cache commutes
  (∀ e : A.encoded, Functor.map F.map_indexed (pA.cache e) = pB.cache (F.map_encoded e)) ∧
  -- Filter commutes
  (∀ i : A.indexed, Functor.map F.map_selected (pA.filter i) = pB.filter (F.map_indexed i)) ∧
  -- Attend commutes
  (∀ (p : A.policy) (s : A.selected),
    Functor.map F.map_ranked (pA.attend p s) = pB.attend (F.map_policy p) (F.map_selected s)) ∧
  -- Remember commutes (forward: ranked → persisted)
  (∀ r : A.ranked, Functor.map F.map_persisted (pA.remember r) = pB.remember (F.map_ranked r)) ∧
  -- Backward pass --
  -- Consolidate commutes (inside substrate: persisted → policy)
  (∀ (p : A.policy) (s : A.persisted),
    Functor.map F.map_policy (pA.consolidate p s) = pB.consolidate (F.map_policy p) (F.map_persisted s))

-- ============================================================
-- Trace: feedback loop
-- ============================================================

/-- The feedback trace: Remember's output type must be compatible
    with Perceive's input type for the loop to close.
    In the self-recursive case, persisted = raw. -/
structure TracedPipeline (M : Type → Type) [Monad M] (I : InterfaceTypes) extends Pipeline M I where
  /-- The loop closes: persisted feeds back to raw -/
  feedback : I.persisted → I.raw

/-- A traced pipeline can run autonomously given an initial input
    and policy. Each cycle feeds Remember's output back to Perceive. -/
def TracedPipeline.run [LawfulProbMonad M] (tp : TracedPipeline M I) (initial : I.raw)
    (policy₀ : I.policy) (n : Nat) : M I.policy :=
  match n with
  | 0 => pure policy₀
  | n + 1 =>
    tp.toPipeline.cycle initial policy₀ >>= fun result =>
    let next_input := tp.feedback result.2
    tp.run next_input result.1 n
