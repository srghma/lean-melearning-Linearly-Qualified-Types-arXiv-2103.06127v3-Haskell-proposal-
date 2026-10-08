# Linear Haskell: the core calculus `λq→` in Lean

This directory formalizes §3 of *Linear Haskell: Practical Linearity in a Higher-Order
Polymorphic Language* (`hlt.typ`), together with the examples of §2.6, §3.3 and §3.5. The
entry point is `RequestProject/LH.lean`. Everything builds without `sorry`. For a comparison
with *Linearly Qualified Types* (formalized in `RequestProject/LQT/`), see `COMPARISON.md` at
the root of the project.

## Binding representation

* **Term variables** use de Bruijn indices. `Tm S m n` is a term with `m` multiplicity
  variables and `n` term variables in scope, so `Tm S m 0` has no free term variables and
  `Tm S 0 0` is closed. `λ_π (x:A). t` binds index `0`. The `j` variables bound by a `case`
  alternative or by a `let` are the last `j` indices of the body.
* **Multiplicity variables** use de Bruijn indices too. `Ty Dn np m` and `Mult m` have `m`
  multiplicity variables in scope, and `∀p` / `λp` bind index `0`.
* **Contexts** are split into types `Γ : Fin n → S.Ty m` and multiplicities
  `u : Fin n → Usage m`. Usage `0` stands for a variable that does not occur in the paper's
  context.

## Where each part of the paper is formalized

| Paper | Lean file | Declarations |
|---|---|---|
| §3.1 Figure 5, multiplicities | `Multiplicity.lean` | `MExp` |
| §3.2 Definition 3.4, equivalence of multiplicities | `Multiplicity.lean` | `MExp.Equiv`, `Mult` (the quotient), `MAlg` |
| §3.2, context addition and scaling | `Multiplicity.lean`, `Typing.lean` | `Usage` (a commutative semiring), pointwise `+` and `•` on usage vectors |
| §3.1 Figure 5, types, datatype declarations, terms | `Syntax.lean` | `Ty`, `Sig`, `Tm` |
| §3.2 Figure 6 and §3.3, typing rules | `Typing.lean` | `HasType` |
| §3.4 metatheory (substitution semantics; see below) | `Weakening.lean`, `MSubst.lean`, `Subst.lean`, `Semantics.lean` | `HasType.weaken_omega`, `HasType.rename`, `HasType.msubst`, `HasType.subst`, `HasType.subst_one`, `Step`, `Value`, `HasType.preservation`, `HasType.progress`, `HasType.type_safety` |
| §3.3, `swap` and `fst` | `Examples.lean` | `swap_typed`, `fst_typed`, `fst_case_one_untypable`, `fst_linear_untypable` |
| §3.5 "Case rule" | `Examples.lean` | `fstPQ_typed`, `unzipUr_typed` |
| §3.5 "Polymorphism & multiplicities" | `Examples.lean` | `id_linear_typed`, `id_unrestricted_typed`, `id_poly_untypable` |
| §3.5 "Subtyping" | `Examples.lean` | `subtyping_rejected`, `subtyping_eta_typed`, `subtyping_poly_typed` |
| §2.6, composition `(◦)` | `Examples.lean` | `compose_typed` |
| §2.2, `foldl write` | `Examples.lean` | `eta_linear_of_unrestricted_untypable` |
| relation to *Linearly Qualified Types* | `Comparison.lean` | `closedMultEquiv`, `closedMultEquiv_mul`, `closedUsageEquiv`, `closedUsageEquiv_add`, `Mult.closed_cases` |

## Deviations from the paper

* **Rule (abs)** is printed with conclusion `A →_q B`. We use `A →_π B`, the multiplicity of
  the binder.
* **Definition 3.4** is stated as a reflexive, transitive relation. We also make it symmetric
  and a congruence, so that it is an equivalence that can be quotiented by.
* **Operational semantics.** The paper's semantics (Launchbury-style with linear environments,
  plus a semantics with in-place mutation) is in its Appendix A, which is not in the supplied
  text. We prove preservation and progress for a call-by-name, substitution-based semantics
  instead. Preservation keeps the multiplicity of every free variable exactly.
* **Examples.** `λq→` has no type polymorphism, so the polymorphic examples are instantiated at
  a unit type `Unit`, and pairs are monomorphic datatypes.
