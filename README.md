# The Natural Framework — Lean 4 formalization

A machine-checked formal specification of a six-stage information processing pipeline derived from temporal flow and bounded storage.

## The claim

Any bounded information processor that persists through time must implement six roles: **Perceive, Cache, Filter, Attend, Consolidate, Remember**. Five compose forward. Consolidate runs backward through the substrate. The ordering is forced by type constraints. Breaking any role in a recursive loop compounds to extinction.

The six roles are monadic kernels (`α → M β`) — morphisms in the Kleisli category of a lawful monad. When `M = Id`, the deterministic case is recovered.

## What the proofs establish vs. what they don't

The Lean proofs **do** establish:
- Given the typed pipeline vocabulary, the forward ordering is unique (`Uniqueness.lean`)
- Removing any postcondition produces failure (`Removal.lean`)
- Contracts compose through monadic kernels (`Handshake.lean`)
- Recursive consolidation preserves postconditions under both induction directions (`Fractal.lean`)
- Deterministic finite transducers have bounded discrimination (`Stochasticity.lean` + `Pigeonhole.lean`)

The Lean proofs **do not** establish:
- That the six roles are the *only possible* decomposition — the roles are built into the type vocabulary, not derived from axioms alone
- Probabilistic claims (entropy, conditioning, measure-theoretic DPI) — the `Support` abstraction reasons about reachability, not probability mass
- That the system axioms encode their physical content — `capacity_bound` and `positive_loss` are trivially satisfiable over Nat (see docstrings)

## Structure

| File | What it formalizes |
|------|-------------------|
| `Support.lean` | `Support` class (possibilistic reachability), `Id` instance |
| `Kleisli.lean` | `Kernel` type, Kleisli composition, category laws from monad laws, deterministic embedding |
| `Axioms.lean` | Four system axioms + one predicate definition (capacity bound, rate mismatch, non-stationarity, positive loss, history matters) + bounded transducer model |
| `Pipeline.lean` | Six roles, interface types, forward/cycle/iterate as monadic kernel composition |
| `Contracts.lean` | Postconditions over support, contract preservation, iteration stability |
| `Boundary.lean` | Perceive forced (capacity bound), Cache forced (rate mismatch), Filter forced (bounded storage), Remember forced (loop closure) |
| `Corollary.lean` | Competitive core, control/data separation, read/write interfaces |
| `DeathConditions.lean` | Three death conditions (broken step, closed loop, decaying input), survival induction |
| `Handshake.lean` | Postcondition-precondition handshake, coupling lemma, information monotonicity, diversity budget, cross-domain functor, traced feedback |
| `Uniqueness.lean` | Forward ordering uniqueness, Consolidate excluded from forward chain |
| `Pigeonhole.lean` | No injection Fin (n+1) → Fin n, pigeonhole collision theorem |
| `Stochasticity.lean` | Determinism → confusion → error chain, state collision via pigeonhole |
| `Removal.lean` | Ten-conjunct falsification table: remove any postcondition, system dies |
| `Induction.lean` | `axiom foundation : life_at_zero ∨ god_is_real`, `life_persists`, `life_requires_all_six` |
| `Fractal.lean` | Recursive consolidation tower, budget termination, `tower_preserves_post` over support |

## What compiles

Everything. Zero `sorry`. Uses Lean's stdlib `LawfulMonad` — no custom monad class. The pigeonhole principle is proved from scratch via element removal — no Mathlib dependency.

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
