# The Natural Framework — Lean formalization

Formalizing a six-step information processing pipeline derived from temporal flow and bounded storage.

## The claim

Any bounded information processor that persists through time must implement six steps: **Perceive, Cache, Filter, Attend, Consolidate, Remember**. The ordering is forced by type constraints. Breaking any step in a recursive loop compounds to extinction.

## Structure

| File | What it formalizes |
|------|-------------------|
| `Pipeline.lean` | Six morphisms, interface types, composition, iteration |
| `Contracts.lean` | Postconditions for each step, iteration stability |
| `Boundary.lean` | Encoding before selection (pigeonhole), selection before persistence |
| `Corollary.lean` | Competitive core, control/data separation, Attend/Consolidate existence |
| `DeathConditions.lean` | Three death conditions, information budget, survival induction |

## Status

Skeleton with core definitions and simple theorems. The hard formalization work ahead:

- [ ] Information-theoretic types (entropy, mutual information, data processing inequality)
- [ ] Lossy morphisms with measurable information loss
- [ ] Diversity as a formal postcondition (DPP or submodular)
- [ ] Traced monoidal category structure (feedback loop)
- [ ] Cross-domain functor (mapping pipeline instances across domains)

## References

- [The Natural Framework](https://june.kim/the-natural-framework) — the derivation
- [The Handshake](https://june.kim/the-handshake) — contracts and formal backbone
- [The Parts Bin](https://june.kim/the-parts-bin) — algorithm catalog

## Build

```
lake build
```

Requires [Lean 4](https://lean-lang.org/) via [elan](https://github.com/leanprover/elan).
