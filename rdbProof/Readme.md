# rdbProof

A concise Coq library modeling how **information sets** evolve under **resource budgets** via closure operators.

**Key Concepts:**

- **Domain**: A poset $(X,\le_X)$ of outcomes.

- **Budgets**: A dcpo $(Λ,\le)$ of resources.

- **Closure operator** $K_λ:𝒫(X)\to𝒫(X).$

- **InformationObject**: any $S⊆X$.

- **CorrectedInformation**: $K_λ(S)$.

- **Contexts**: fixed‑points $C=K_λ(C)$, forming a complete lattice.

## Files

1. **RDB.v**: Defines $(X,Λ)$, closure axioms, contexts, and lattice structure.
2. **CatV.v**: Abstract closure operators & supremum construction.
3. **PresheafFam.v**: Category of closure ops and budget‑indexed functor.
4. **PresheafOfContexts.v**: Contravariant presheaf of contexts (sup→inf).
5. **Composition.v**: Composes two systems into a new closure operator.
