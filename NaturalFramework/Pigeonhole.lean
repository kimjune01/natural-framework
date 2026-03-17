/-!
# Pigeonhole Principle

No injection from `Fin (n+1)` to `Fin n`. Therefore among `N+1` values
in `Fin N`, at least two must collide.

Proved from scratch by induction on `n` with element removal.
No Mathlib dependency.
-/

-- ============================================================
-- Element removal: Fin (n+1) \ {v} → Fin n
-- ============================================================

/-- Remove element `v` from `Fin (n+1)`, compressing to `Fin n`.
    Elements below `v` keep their index; elements above shift down by 1. -/
private def compress {n : Nat} (v x : Fin (n + 1)) (h : x ≠ v) : Fin n :=
  if hlt : x.val < v.val then
    ⟨x.val, by omega⟩
  else
    ⟨x.val - 1, by
      have : x.val ≠ v.val := fun heq => h (Fin.ext heq)
      have := x.isLt
      omega⟩

/-- `compress` is injective on inputs distinct from `v`. -/
private theorem compress_injective {n : Nat} (v x y : Fin (n + 1))
    (hx : x ≠ v) (hy : y ≠ v)
    (heq : compress v x hx = compress v y hy)
    : x = y := by
  have hxv : x.val ≠ v.val := fun h => hx (Fin.ext h)
  have hyv : y.val ≠ v.val := fun h => hy (Fin.ext h)
  unfold compress at heq
  -- Four cases: each of x, y is above or below v
  split at heq <;> split at heq <;> {
    simp only [Fin.mk.injEq] at heq
    exact Fin.ext (by omega)
  }

-- ============================================================
-- Core: no injection Fin (n+1) → Fin n
-- ============================================================

/-- There is no injection from `Fin (n+1)` to `Fin n`.
    Proof by induction on `n` with element removal at each step. -/
theorem Fin.no_injection (n : Nat)
    : ∀ g : Fin (n + 1) → Fin n, ¬ Function.Injective g := by
  induction n with
  | zero =>
    intro g _
    exact Fin.elim0 (g ⟨0, by omega⟩)
  | succ k ih =>
    intro g hg
    -- g : Fin (k+2) → Fin (k+1), injective
    -- Embed i : Fin (k+1) into Fin (k+2) as ⟨i.val, _⟩, which ≠ ⟨k+1, _⟩
    have hne : ∀ i : Fin (k + 1),
        (⟨i.val, by omega⟩ : Fin (k + 2)) ≠ ⟨k + 1, by omega⟩ := by
      intro i h
      simp only [Fin.mk.injEq] at h
      exact absurd h (by omega)
    -- Therefore g(embed i) ≠ g(⟨k+1, _⟩) by injectivity
    have hgv : ∀ i : Fin (k + 1),
        g ⟨i.val, by omega⟩ ≠ g ⟨k + 1, by omega⟩ := by
      intro i hfv
      exact absurd (hg hfv) (hne i)
    -- Build g' : Fin (k+1) → Fin k by removing g(⟨k+1,_⟩) from codomain
    let g' (i : Fin (k + 1)) : Fin k :=
      compress (g ⟨k + 1, by omega⟩) (g ⟨i.val, by omega⟩) (hgv i)
    -- g' is injective
    have hg' : Function.Injective g' := by
      intro a b hab
      have h1 := compress_injective (g ⟨k + 1, by omega⟩) _ _ (hgv a) (hgv b) hab
      have h2 := hg h1
      simp only [Fin.mk.injEq] at h2
      exact Fin.ext h2
    -- Contradicts IH
    exact ih g' hg'

-- ============================================================
-- Pigeonhole: collision among N+1 values in Fin N
-- ============================================================

/-- Among N+1 values in Fin N, at least two must collide. -/
theorem pigeonhole {N : Nat} (f : Fin (N + 1) → Fin N)
    : ∃ i j : Fin (N + 1), i < j ∧ f i = f j :=
  Classical.byContradiction fun hall =>
    Fin.no_injection N f fun a b heq =>
      Classical.byContradiction fun hne =>
        hall <| (Nat.lt_or_gt_of_ne (fun h => hne (Fin.ext h))).elim
          (fun h => ⟨a, b, h, heq⟩)
          (fun h => ⟨b, a, h, heq.symm⟩)

/-- Pigeonhole for Nat-indexed sequences: among values f(0), ..., f(N),
    at least two in Fin N must collide. -/
theorem pigeonhole_nat {N : Nat} (_ : N > 0) (f : Nat → Fin N)
    : ∃ i j : Nat, i < N + 1 ∧ j < N + 1 ∧ i < j ∧ f i = f j :=
  match @pigeonhole N (fun k => f k.val) with
  | ⟨i, j, hij, hfij⟩ => ⟨i.val, j.val, i.isLt, j.isLt, hij, hfij⟩
