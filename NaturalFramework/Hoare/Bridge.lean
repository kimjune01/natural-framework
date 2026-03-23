import NaturalFramework.Hoare.Core

/-!
# Hoare Logic Layer — Bridge to Contracts

Connects Hoare triples to the existing contract and handshake
infrastructure. Shows that `ContractPreserving` is a special case
of `Triple`, and that handshakes compose via the triple rule.

## Main definitions

- `contract_is_triple` — contract preservation is a triple with trivial precondition
- `handshake_enables_comp` — handshake-compatible stages compose
- `triple_counterexample` — nontriviality: a kernel can fail a triple
-/

/-- Contract preservation restated as a Hoare triple with precondition `True`.
    Definitional — both sides unfold to the same quantifier structure. -/
theorem contract_is_triple [Monad M] [Support M]
    {f : Kernel M α β} {Q : Contract β}
    : ContractPreserving f Q ↔ Triple (fun _ => True) f Q := by
  constructor
  · intro hcp a _ b hsup
    exact hcp a b hsup
  · intro ht a b hsup
    exact ht a True.intro b hsup

/-- Handshake-compatible stages compose: if `f` establishes the
    handshake postcondition and `k` requires the handshake precondition,
    sequential composition carries `P` to `R`. -/
theorem handshake_enables_comp [Monad M] [LawfulMonad M] [Support M]
    {P : α → Prop} {R : γ → Prop}
    {f : Kernel M α β} {k : Kernel M β γ}
    (h : Handshake β)
    (hf : Triple P f h.post)
    (hk : Triple h.pre k R)
    : Triple P (Kernel.comp f k) R := by
  exact triple_comp hf (triple_consequence h.compatible (fun _ hq => hq) hk)

-- ============================================================
-- Nontriviality: a kernel can FAIL a triple
-- ============================================================

/-- A kernel that maps `()` to `false` in `Id`. -/
private def badKernel : Kernel Id Unit Bool := fun _ => (false : Bool)

/-- The triple `{True} badKernel {· = true}` does NOT hold.
    Demonstrates that not every kernel satisfies every triple —
    the proof system is nontrivial. -/
theorem triple_counterexample : ¬ Triple (fun (_ : Unit) => True) badKernel (· = true) := by
  intro h
  have := h () True.intro false ((Support.support_pure false false).mpr rfl)
  exact absurd this (by decide)
