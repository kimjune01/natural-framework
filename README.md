# The Natural Framework — Lean 4 formalization

Formalizing a six-step information processing pipeline derived from temporal flow and bounded storage.

## The claim

Any bounded information processor that persists through time must implement six roles: **Perceive, Cache, Filter, Attend, Consolidate, Remember**. Five compose forward. Consolidate runs backward through the substrate. The ordering is forced by type constraints. Breaking any role in a recursive loop compounds to extinction.

## Structure

| File | What it formalizes |
|------|-------------------|
| `Axioms.lean` | Five physics axioms (Landauer, rate mismatch, non-stationarity, dissipation, history matters) + bounded transducer model |
| `Pipeline.lean` | Six roles, interface types, forward/cycle/iterate composition |
| `Contracts.lean` | Postconditions, contract preservation, iteration stability |
| `Boundary.lean` | Perceive forced (Landauer), Cache forced (rate mismatch), Filter forced (bounded storage), Remember forced (loop closure) |
| `Corollary.lean` | Competitive core, control/data separation, read/write interfaces |
| `DeathConditions.lean` | Three death conditions (broken step, closed loop, decaying input), survival induction |
| `Handshake.lean` | Postcondition-precondition handshake, coupling lemma, DPI, diversity budget, cross-domain functor, traced feedback |
| `Uniqueness.lean` | Forward ordering uniqueness, Consolidate excluded from forward chain |
| `Stochasticity.lean` | Determinism → confusion → error chain |
| `Removal.lean` | Ten-conjunct falsification table: remove any postcondition, system dies |
| `Induction.lean` | Foundation axiom (disjunction), `life_persists`, `life_requires_all_six` |
| `Fractal.lean` | Recursive consolidation tower, DPI termination, `tower_preserves_post` |

## What compiles

Everything except one `sorry`: pigeonhole in `state_collision` (needs Mathlib's `Fintype`). Four fields carry `True` placeholders pending Mathlib's measure theory: `AttendContract.bounded`, `ConsolidateContract.lossy`, `EchoChamber.novel_items_zero`, `DegradedConsolidate.kernel_broken`.

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
