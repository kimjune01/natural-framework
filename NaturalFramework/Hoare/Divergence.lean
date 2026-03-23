import NaturalFramework.Hoare.Core

/-!
# Divergence Bridge — NonExpanding as a Family of Hoare Triples

Shows that NonExpanding (information measure doesn't increase) is
equivalent to preserving every information-threshold contract.

This bridges Sato-Katsumata (2023): divergences on a monad give a
metric on morphism spaces. NonExpanding is the zero-divergence case —
the morphism doesn't increase the measure. Stating it as a family of
Hoare triples connects the metric view to the program logic view.

## Status: Exact (for the threshold characterization)

The equivalence is tight: NonExpanding ↔ ∀ n, {measure ≤ n} f {measure ≤ n}.
This is not the full Sato-Katsumata divergence framework (which uses
arbitrary V-enrichment), but it exactly characterizes NonExpanding in
terms of Hoare triples. The composition theorem follows from existing
`non_expanding_compose`.
-/

/-- NonExpanding is equivalent to preserving all information-threshold
    contracts. A kernel that doesn't increase measure preserves every
    upper bound on measure — and conversely.

    Forward: mβ.b ≤ mα.a ≤ n, so mβ.b ≤ n.
    Backward: pick n = mα.measure a, get mβ.b ≤ mα.a. -/
theorem nonExpanding_iff_threshold_triple [Monad M] [Support M]
    {f : Kernel M α β} {mα : InfoMeasure α} {mβ : InfoMeasure β} :
    NonExpanding f mα mβ ↔
      ∀ n : Nat, Triple (fun a => mα.measure a ≤ n) f (fun b => mβ.measure b ≤ n) := by
  constructor
  · intro hne n a ha b hb
    have := hne a b hb
    omega
  · intro htr a b hb
    have := htr (mα.measure a) a (Nat.le_refl _) b hb
    omega
