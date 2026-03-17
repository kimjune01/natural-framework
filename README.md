# The Natural Framework — Lean 4 formalization

Formalizing a six-step information processing pipeline derived from temporal flow and bounded storage.

## The claim

Any bounded information processor that persists through time must implement six roles: **Perceive, Cache, Filter, Attend, Consolidate, Remember**. Five compose forward. Consolidate runs backward through the substrate. The ordering is forced by type constraints. Breaking any role in a recursive loop compounds to extinction.

The six roles are morphisms in Stoch — the Kleisli category of a probability monad. When `M = Id`, the deterministic case is recovered.

## Structure

| File | What it formalizes |
|------|-------------------|
| `ProbabilityMonad.lean` | `LawfulProbMonad` class, `Support` class, `Id` instances |
| `Stoch.lean` | `Kernel` type, Kleisli composition, category laws from monad laws, deterministic embedding |
| `Axioms.lean` | Five physics axioms (Landauer, rate mismatch, non-stationarity, dissipation, history matters) + bounded transducer model |
| `Pipeline.lean` | Six roles, interface types, forward/cycle/iterate as stochastic kernel composition |
| `Contracts.lean` | Postconditions over support, contract preservation, iteration stability |
| `Boundary.lean` | Perceive forced (Landauer), Cache forced (rate mismatch), Filter forced (bounded storage), Remember forced (loop closure) |
| `Corollary.lean` | Competitive core, control/data separation, read/write interfaces |
| `DeathConditions.lean` | Three death conditions (broken step, closed loop, decaying input), survival induction |
| `Handshake.lean` | Postcondition-precondition handshake, coupling lemma, DPI over support, diversity budget, cross-domain functor, traced feedback |
| `Uniqueness.lean` | Forward ordering uniqueness, Consolidate excluded from forward chain |
| `Pigeonhole.lean` | No injection Fin (n+1) → Fin n, pigeonhole collision theorem |
| `Stochasticity.lean` | Determinism → confusion → error chain, state collision via pigeonhole |
| `Removal.lean` | Ten-conjunct falsification table: remove any postcondition, system dies |
| `Induction.lean` | Foundation axiom (disjunction), `life_persists`, `life_requires_all_six` |
| `Fractal.lean` | Recursive consolidation tower, DPI termination, `tower_preserves_post` over support |

## What compiles

Everything. Zero `sorry`. The pigeonhole principle is proved from scratch via element removal — no Mathlib dependency.

## Build

```
lake build
```

Requires [Lean 4](https://lean-lang.org/) via [elan](https://github.com/leanprover/elan).

## References

- [The Natural Framework](https://june.kim/the-natural-framework) — the derivation
- [The Handshake](https://june.kim/the-handshake) — contracts and formal backbone
- [The Parts Bin](https://june.kim/the-parts-bin) — algorithm catalog

## License

AGPL-3.0
