---
title: "ACT 2026 Abstract Draft"
---

# A Lean-Verified Crosswalk Between Stochastic Semantics, Contracts, and Hoare Logic

June Kim

## Abstract

We present a Lean 4 artifact (about 2,800 lines, zero `sorry`, standard library only) that formalizes a stochastic information-processing pipeline and uses it to assemble a precise crosswalk across several communities in applied category theory. The core development models six stages of processing as morphisms in the Kleisli category of a lawful monad, with stage contracts represented as predicates preserved by composition. Within Lean, we prove a contract-composition theorem, derive two contracts as optimality conditions, reconstruct pigeonhole and stochasticity arguments from first principles, and formalize a recursive consolidation tower with budget-based termination.

A key feature of the artifact is a compiled Hoare-logic layer: three Lean files develop Hoare triples, weakest preconditions, and a bridge theorem showing that the original contract-preservation predicate is equivalent to a Hoare triple with trivial precondition. The same pipeline properties are proved from two independent angles — one functional, one imperative — and their equivalence is machine-checked. The crosswalk between stochastic semantics, contracts, and program logic is compiled, not just described.

The resulting dictionary includes several exact identifications. The ambient category of the development is the Kleisli category of a distribution monad, matching the finite-stochastic setting of Markov categories (Fritz 2020). The Lean `Support` typeclass aligns with the possibilistic shadow of Fritz, Perrone, and Rezagholi (2021): the support-composition lemma is the monad multiplication for supp : V ⇒ H. Recent work showing that Stoch is a posetal imperative category (Bonchi, Di Lavore, Roman, Staton 2025, Corollary 76, Theorem 79) fits the artifact: the Lean bridge theorem identifies behavioral contracts on stochastic morphisms with classical Hoare reasoning. The Hoare layer includes a nontriviality counterexample, ruling out vacuous readings of the specification.

Other correspondences are plausible rather than exact. The contract predicate is close to a Hoare postcondition in graded Hoare logic (Gaboardi et al. 2021); the handshake condition between adjacent pipeline stages resembles the restricted pointwise order in graded-monadic program logics (Kura et al. 2026); and neighboring ideas appear in categorical cybernetics, including selection relations on parametrised optics (Capucci et al. 2021) and compositional equilibrium predicates (Ghani, Hedges et al. 2018). The crosswalk places exact identifications, plausible translations, and genuine mismatches in one verified framework.

Once assembled, this dictionary surfaces concrete open problems:

- **Counting monad.** The free ℕ-semimodule monad (Kidney & Wu 2021) composed with the support monad morphism would track support cardinality through stochastic composition, connecting Leinster's magnitude (2021) to Fritz's possibilistic shadow. This composite has not been constructed.
- **Categorical DPPs.** Determinantal point processes have no categorical semantics. The exterior algebra functor exists; the connection to Markov categories does not.
- **Coding theorems.** Fritz's categorical entropy and data processing inequality have no accompanying achievability or rate-distortion results inside Markov categories.

The talk is aimed at researchers who work in one of these formalisms but not the others.

The Lean development, vocabulary crosswalk, and full reference table are publicly available at github.com/kimjune01/natural-framework and june.kim/framework-lexicon.

## References

- Bonchi, Di Lavore, Roman, Staton. Program Logics via Distributive Monoidal Categories. arXiv:2507.18238, 2025.
- Capucci, Gavranović, Hedges, Rischel. Towards Foundations of Categorical Cybernetics. ACT 2021.
- Fritz. A synthetic approach to Markov kernels. Advances in Mathematics, 2020.
- Fritz, Perrone, Rezagholi. Probability, valuations, hyperspace: Three monads on Top and the support as a morphism. MSCS, 2021.
- Gaboardi, Katsumata, Orchard, Sato. Graded Hoare Logic and its Categorical Semantics. ESOP 2021.
- Ghani, Kupke, Lambert, Forsberg. Compositional Game Theory with Mixed Strategies. APLAS 2020.
- Kidney, Wu. Algebras for Weighted Search. ICFP 2021.
- Kura, Gaboardi, Sekiyama, Unno. A Category-Theoretic Framework for Dependent Effect Systems. ESOP 2026.
- Leinster. Entropy and Diversity: The Axiomatic Approach. Cambridge, 2021.
- Liell-Cock, Staton. Compositional Imprecise Probability. POPL 2025.
- Sato, Katsumata. Divergences on Monads for Relational Program Logics. MSCS 2023.
