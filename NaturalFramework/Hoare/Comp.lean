import NaturalFramework.Hoare.Bridge

/-!
# Hoare Logic Layer — Full Pipeline Composition

Chains all five forward stages through their handshakes using the
COMP rule with real pre/postconditions — not just the `⊤` version.

Stage N's postcondition is stage N+1's precondition. This is the
restricted pointwise order from Kura–Gaboardi et al. (2026, Def 7),
verified in Lean.

## Main definitions

- `forward_triple` — full forward pipeline satisfies `{P_raw} forward {Q_ranked}`
  by threading handshakes through all five stages
- `pipeline_comp_chain` — the explicit four-handshake chain
-/

-- ============================================================
-- Individual stage triples with real pre/postconditions
-- ============================================================

/-- A pipeline where each stage satisfies a Hoare triple with
    the handshake threading through: post of N = pre of N+1. -/
structure PipelineTriples (M : Type → Type) [Monad M] [Support M]
    (I : InterfaceTypes) (p : Pipeline M I) where
  /-- Predicates at each interface point -/
  P_raw : I.raw → Prop
  Q_encoded : I.encoded → Prop
  Q_indexed : I.indexed → Prop
  Q_selected : I.selected → Prop
  Q_ranked : I.ranked → Prop
  /-- Each stage satisfies its triple -/
  h_perceive : Triple P_raw p.perceive Q_encoded
  h_cache : Triple Q_encoded p.cache Q_indexed
  h_filter : Triple Q_indexed p.filter Q_selected
  h_attend : ∀ pol : I.policy, Triple Q_selected (p.attend pol) Q_ranked

-- ============================================================
-- Multi-stage composition (convenience wrappers around triple_comp)
-- ============================================================

/-- Alias for `triple_comp`. -/
theorem two_stage_comp [Monad M] [LawfulMonad M] [Support M]
    {f : Kernel M α β} {g : Kernel M β γ}
    {P : α → Prop} {R : β → Prop} {Q : γ → Prop}
    (hf : Triple P f R) (hg : Triple R g Q)
    : Triple P (Kernel.comp f g) Q :=
  triple_comp hf hg

-- ============================================================
-- Three-stage chain
-- ============================================================

/-- Three-stage triple_comp. -/
theorem three_stage_comp [Monad M] [LawfulMonad M] [Support M]
    {f : Kernel M α β} {g : Kernel M β γ} {h : Kernel M γ δ}
    {P : α → Prop} {R1 : β → Prop} {R2 : γ → Prop} {Q : δ → Prop}
    (hf : Triple P f R1) (hg : Triple R1 g R2) (hh : Triple R2 h Q)
    : Triple P (Kernel.comp (Kernel.comp f g) h) Q :=
  triple_comp (triple_comp hf hg) hh

-- ============================================================
-- Four-stage chain (the full forward pipeline minus attend)
-- ============================================================

/-- Four-stage triple_comp. Generic — not specific to pipeline stages. -/
theorem four_stage_comp [Monad M] [LawfulMonad M] [Support M]
    {f1 : Kernel M α β} {f2 : Kernel M β γ}
    {f3 : Kernel M γ δ} {f4 : Kernel M δ ε}
    {P : α → Prop} {R1 : β → Prop} {R2 : γ → Prop}
    {R3 : δ → Prop} {Q : ε → Prop}
    (h1 : Triple P f1 R1) (h2 : Triple R1 f2 R2)
    (h3 : Triple R2 f3 R3) (h4 : Triple R3 f4 Q)
    : Triple P (Kernel.comp (Kernel.comp (Kernel.comp f1 f2) f3) f4) Q :=
  triple_comp (triple_comp (triple_comp h1 h2) h3) h4

-- ============================================================
-- Full forward pipeline triple
-- ============================================================

/-- The forward pipeline as a single Kleisli composition. -/
def Pipeline.forwardKernel [Monad M] (p : Pipeline M I) (policy : I.policy)
    : Kernel M I.raw I.ranked :=
  Kernel.comp (Kernel.comp (Kernel.comp p.perceive p.cache) p.filter) (p.attend policy)

/-- The forward pipeline satisfies `{P_raw} forward {Q_ranked}`
    when each stage satisfies its triple. Applies four_stage_comp
    to the pipeline's specific stages. -/
theorem forward_triple [Monad M] [LawfulMonad M] [Support M]
    {I : InterfaceTypes} {p : Pipeline M I}
    (t : PipelineTriples M I p) (policy : I.policy)
    : Triple t.P_raw (p.forwardKernel policy) t.Q_ranked :=
  four_stage_comp t.h_perceive t.h_cache t.h_filter (t.h_attend policy)

/-- Definitional: `forwardKernel` and `Pipeline.forward` unfold to the same bind chain. -/
theorem forwardKernel_eq_forward [Monad M] [LawfulMonad M] [Support M]
    (p : Pipeline M I) (policy : I.policy) (input : I.raw)
    : p.forwardKernel policy input = p.forward input policy := by
  simp [Pipeline.forwardKernel, Pipeline.forward, Kernel.comp, bind_assoc]

/-- Corollary: the actual `Pipeline.forward` satisfies the triple.
    Connects the abstract kernel composition to the concrete pipeline. -/
theorem forward_triple' [Monad M] [LawfulMonad M] [Support M]
    {I : InterfaceTypes} {p : Pipeline M I}
    (t : PipelineTriples M I p) (policy : I.policy)
    (input : I.raw) (ranked : I.ranked)
    (hpre : t.P_raw input)
    (hsup : Support.support (p.forward input policy) ranked)
    : t.Q_ranked ranked := by
  have heq := forwardKernel_eq_forward p policy input
  have htriple := forward_triple t policy
  exact htriple input hpre ranked (heq ▸ hsup)
