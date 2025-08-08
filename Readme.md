# Budget-Indexed Closure Operators (Coq)

Formalisation of **budget-indexed closure operators (BICOs)** and the **canonical operator** built from probabilistic "guaranteed regions." Includes single-budget, two-budget (decomposition), and multi-channel variants.

## Why care (short version)

* Models how "more budget => more closure" in a clean lattice/Scott-continuous way.
* Canonical construction: $K_{\lambda,p}(A)=A\cup \mathrm{GR}^+_{\lambda,p}$ with proofs of A1–A5.
* Useful as a minimal, compositional semantics for information growth/feasibility under resources.

## What's here

* `BICO_Formalisation.v` – all definitions & proofs:

  * `SETTING` (lattice & order setup)
  * `BICO` (axioms A1–A5, plateau criterion)
  * `CANONICAL_CONSTRUCTION` (probability thresholds → canonical operator)
  * `BICO_Category_Perspective` (operator algebra, dcpo, composition)
  * `DECOMPOSITION_OF_LOSS` (two-budget split)
  * `MULTI_CHANNEL_DECOMPOSITION` (per-bucket budgets; hull operator)

*Work in progress; structure is stable, polishing ongoing.*

## Requirements

* Coq (8.17+ recommended)
* SSReflect/MathComp components (for `ssreflect`, `ssrfun`, `ssrbool`)
* Standard library (Ensembles, Reals, Classical)

## Build / run proofs

"`bash
# simplest: compile the whole file
coqc BICO_Formalisation.v
```
## Status

* Proofs for `K_can_is_BICO`, two-budget `K_bar` BICO, and multi-channel BICO included.
* Text and comments still being tightened; expect minor refactors.

## Contact / citation

If you use this, please cite the repo. Feedback by issues/PRs is welcome once the draft settles.
