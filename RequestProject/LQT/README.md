# Linearly Qualified Types — Lean formalization

This directory formalizes the paper *Linearly Qualified Types* (`linear-constraints.tex`,
typing rules in `ott.tex`): the qualified type system with linear constraints, constraint
generation, the constraint solver, and the desugaring into a linear core calculus.
Type polymorphism is included (`∀ā` in type schemes and `∃ā` in existential types).
The entry point is `RequestProject/LQT.lean`, which imports everything. All results build
without `sorry` and depend only on the standard axioms (`propext`, `Classical.choice`,
`Quot.sound`).

## Binding representation

* **Expression variables** use de Bruijn indices: `Tm sig k n` is the type of expressions with
  `k` type variables and `n` expression variables in scope, so `Tm sig 0 0` is the type of
  closed expressions. Contexts are `Fin n → Scheme P k`, and the paper's context operations
  (`Γ₁ + Γ₂`, `π·Γ`) become *usage vectors* `Fin n → Usage` over the semiring `{0, 1, ω}`.
* **Type variables** also use de Bruijn indices: `Ty P k` is the type of types with `k` type
  variables in scope (`Ty P 0` holds closed types). A binder `∀ā` / `∃ā` binds a *block* of
  `j` variables. Inside the binder the variables in scope are `Fin (k + j)`, and the bound
  ones are the last `j`.
* Constraints, contexts and domains are indexed by `k` in the same way (`Atom P k`,
  `SConstr (Atom P k)`, `Wanted A k`, `LDomain A := (k : Nat) → Domain (A k)`).

## Where each part of the paper is formalized

Section, figure, definition and lemma numbers refer to the paper as typeset from the supplied
source `linear-constraints.tex`; each comment also gives the title, so the parts can be found
even in a version with different numbering.  Inside the Lean files, each part of the paper is
delimited by a pair of comments

```
-- [PAPER ▶ START] §6.2 › Lemma 6.4 "Soundness of constraint generation" ...
...
-- [PAPER ◀ END] §6.2 › Lemma 6.4
```

and material that has no counterpart in the paper (de Bruijn infrastructure, helper lemmas,
non-vacuity checks, findings about the paper) is delimited by
`-- [NOT IN PAPER ▶ START]` / `-- [NOT IN PAPER ◀ END]`.  Search for `[PAPER` to list them.
Sections 1, 3, 4, 8, 9, 10 of the paper (introduction, examples, applications, implementation
in GHC, related work, conclusion) contain no formal material and are not formalized.

| Paper | Lean file | Main declarations |
|---|---|---|
| §2.1 "Multiplicities" | `Basic.lean` | `Mult` |
| §5.1, Definition 5.1 "Atomic constraints" | `Syntax.lean` | `Atom` |
| §5.1, Definition 5.2 "Simple constraints" | `Basic.lean` | `SConstr`, `SConstr.atom` |
| §5.1, scaling `π·Q` (before Lemma 5.4) | `Basic.lean` | `SConstr.smul` |
| §5.1, Definition 5.3 "Entailment relation" | `Entailment.lean`, `Basic.lean` | `Domain`, `SConstr.InDup` |
| §5.1, Figure 4 "Requirements for the entailment relation" | `Entailment.lean` | `Domain.CommonLaws`, `Domain.PaperLaws`, `Domain.Lawful` |
| §5.1, Lemma 5.4 "Scaling" | `Entailment.lean` | `Domain.Lawful.scaling` |
| §5.1, Lemma 5.5 "Inversion of scaling" | `Entailment.lean` | `Domain.Lawful.scaling_inv`, `Domain.PaperLaws.scaling_inv` |
| §5.1, Corollary 5.6 "Linear assumptions" | `Entailment.lean` | `Domain.Lawful.linear_assumptions`, `Domain.PaperLaws.linear_assumptions` |
| §5.2, Figure 5 "Grammar of the qualified type system" | `Syntax.lean` | `Ty`, `Scheme`, `DataSig`, `Tm` |
| §5.2, Figure 6 "Qualified type system" | `Typing.lean` | `HasType` |
| §6.1 "Wanted constraints" (grammar, scaling) | `Wanted.lean` | `Wanted`, `Wanted.smul` |
| §6.1, Figure 7 "Wanted-constraint entailment" | `Wanted.lean` | `LDomain.WEntails` |
| §6.1, Lemma 6.1 "Inversion" | `Wanted.lean` | `LDomain.Lawful.inv_tensor`, `inv_amp`, `inv_impl`, `LDomain.PaperLaws.inv_impl` |
| §6.1, Lemma 6.2 "Scaling" | `Wanted.lean` | `LDomain.Lawful.wentails_scaling` |
| §6.1, Lemma 6.3 "Inversion of scaling" | `Wanted.lean` | `LDomain.Lawful.wentails_scaling_inv`, `LDomain.PaperLaws.wentails_scaling_inv` |
| §6.2, Figure 8 "Constraint generation" | `Generation.lean` | `Gen`, `withAll` |
| §6.2, Lemma 6.4 "Soundness of constraint generation" | `Generation.lean` | `LDomain.Lawful.gen_sound` |
| §6.3, atomic-solver judgement | `Solver.lean` | `AtomSolver` |
| §6.3, Lemma 6.5 "Constraint solver soundness" | `Solver.lean` | `LDomain.Lawful.solve_sound`, `solve_sound_strong` |
| §6.3, Property 6.6 "Atomic-constraint solver soundness" | `Solver.lean` | `AtomSolver.PaperSound` (and the stronger `AtomSolver.Sound`) |
| §6.3.1, Figure 9 "Constraint solver" | `Solver.lean` | `Solve` |
| §6.3.2, Figure 10a "Entailment relation" | `FreeDomain.lean` | `freeEntails`, `freeDomain`, `fig10a_*` |
| §6.3.2, Figure 10b "Atomic-constraint solver" | `Solver.lean` | `simpleSolver` |
| §7.1, Figure 11 "Core calculus (subset)"; App. A.1, Figures 13 and 14 | `Core.lean` | `CTy`, `CScheme`, `CTm`, `CHasType` |
| §7.2.1 "Evidence", Figure 12a "Evidence passing" | `Core.lean` | `CTy.ev`, `Prim`, `PrimTy` |
| §7.2.2 "Translating types" | `Core.lean` | `Ty.ds`, `Scheme.ds` |
| §7.2.3 "Translating terms", Figure 12b; App. A.2, Figure 15 "Desugaring" | `Desugar.lean` | `desugarAt`, `desugar`, `dsLet`, `dsLetSig` |
| §7.2.3, Theorem 7.1 "Desugaring" | `DesugarTyping.lean` | `desugar_typed` (induction: `desugarAt_typed`) |
| App. B.5, Lemma B.1 (`π·(ρ·Q) = (π⋅ρ)·Q`) | `Basic.lean` | `mul_smul` field of the `DistribMulAction Mult (SConstr A)` instance |
| App. B.6, Lemma B.2 "`𝒟` discarding" | `Entailment.lean` | `Domain.Lawful.discard_dup`, `weaken_dup` |
| App. B.6, Lemma B.3 "`𝒟` duplication" | `Entailment.lean` | `Domain.Lawful.dup_dup`, `dup_contraction` |
| App. B.6, Lemma B.4 "Transitive tensor decomposition" | `Entailment.lean` | `Domain.Lawful.transitive_tensor_decomposition` |
| App. B.6, Lemma B.5 "Weakening of wanteds" | `Wanted.lean` | `LDomain.Lawful.wentails_weaken` |
| App. B.6, Lemma B.6 (`π·(ρ·C) = (π⋅ρ)·C`) | `Wanted.lean` | `Wanted.smul_smul` |

Files with no counterpart in the paper: `Map.lean`, `UsageVec.lean`, `FreeLDomain.lean`,
`DesugarTypingAux.lean`.

## Files

| File | Content (paper section) |
|---|---|
| `Basic.lean` | multiplicities, usages, simple constraints `Q = (U, L)` (§2.1, §5.1 Def. 5.2) |
| `Entailment.lean` | constraint domains and the laws of Fig. 4, the repaired laws, Lemmas 5.4/5.5, Corollary 5.6, Lemmas B.2–B.4 |
| `FreeDomain.lean` | the stripped-down domain of §6.3.2 / Fig. 10a; satisfiability of the laws |
| `Map.lean` | mapping over the atoms of a constraint (used for renaming/substitution) |
| `Wanted.lean` | leveled domains, wanted constraints `C`, `Q ⊢ C` (Fig. 7), Lemmas 6.1–6.3, B.5, B.6 |
| `FreeLDomain.lean` | lawful leveled domains exist (`freeLDomain_lawful`, `predLDomain_lawful`) |
| `Syntax.lean` | types, schemes, atoms, data signatures, expressions (Fig. 5, Def. 5.1) |
| `Typing.lean` | the qualified type system `Q ; Γ ⊢ e : τ` (Fig. 6) |
| `Generation.lean` | constraint generation (Fig. 8), **Lemma 6.4** (`gen_sound`) |
| `Solver.lean` | constraint solver (Fig. 9, 10b), **Lemma 6.5** (`solve_sound`), Property 6.6, end-to-end `infer_sound`, atomic solver soundness |
| `Core.lean` | linear core calculus (Fig. 11 / App. A.1, Figs. 13–14) with polymorphic `let` and existential pairs; translation of types (§7.2.2) |
| `UsageVec.lean` | usage-vector algebra for renamings |
| `Desugar.lean` | desugaring `⟦d⟧_z` (Fig. 12b / App. A.2, Fig. 15) |
| `DesugarTypingAux.lean`, `DesugarTyping.lean` | **Theorem 7.1** (`desugar_typed`) |

## Main results

* `LQT.desugar_typed` (Theorem 7.1): if `d : Q ; Γ ⊢ e : τ` then
  `⟦Γ⟧, z :₁ ⟦Q⟧ ⊢ ⟦d⟧_z : ⟦τ⟧` in the core calculus.
* `LQT.LDomain.Lawful.gen_sound` (Lemma 6.4): if `Γ ⊢ᵢ e : τ ⇝ C` and `Q ⊢ C`, then
  `Q ; Γ ⊢ e : τ`.
* `LQT.LDomain.Lawful.solve_sound` (Lemma 6.5) and `LQT.LDomain.Lawful.infer_sound`
  (generation followed by solving is sound).
* `LQT.simpleSolver_sound`: the atomic solver of Fig. 10b satisfies the solver property.
* `LQT.LDomain.Lawful.inv_tensor/inv_amp/inv_impl` (Lemma 6.1),
  `wentails_scaling` (6.2), `wentails_scaling_inv` (6.3), `Wanted.smul_smul` (B.6),
  `wentails_weaken` (B.5).
* `LQT.Domain.PaperLaws.dup_eq_empty`, `LQT.paper_scaling_inv_fails`,
  `LQT.freeDomain_lawful`, `LQT.freeLDomain_lawful`, `LQT.predLDomain_lawful` (see below).

## Deviations from the paper

1. **Law (7) of Figure 4 is repaired.** As stated, the twelve laws force `𝒟 = ∅`
   (`Domain.PaperLaws.dup_eq_empty`). We therefore work with `Domain.Lawful`, in which law (7)
   holds "up to `𝒟`", the same way the paper states Lemma 6.1. Every domain satisfying the
   paper's laws is lawful (`PaperLaws.toLawful`), and the paper's exact statements are
   recovered for such domains (`PaperLaws.*`). The repaired laws are satisfiable with a
   non-empty `𝒟` (`freeDomain_lawful`). The paper's Lemma 5.5 fails as soon as `𝒟 ≠ ∅`
   (`paper_scaling_inv_fails`).
2. **Transitive tensor decomposition** is stated with the duplicable part shared between both
   sides, which is the form the proofs need.
3. **Atomic solver property (Property 6.6) is strengthened.** We require that the *consumed*
   assumptions entail the atom (`AtomSolver.Sound`). This implies the paper's property
   (`Sound.paperSound`), and the solver of Fig. 10b satisfies it. With only the paper's
   property, the S_ImplOne case of Lemma 6.5 would need a cancellation law that Fig. 4 does
   not provide.
4. **Type variables and implication constraints.** The fresh type variables of G_Unpack and
   G_LetSig are bound explicitly in implication constraints `π·∀ā.(Q ⊸ C)` (`Wanted.impl`).
   The domain is a family of domains, one per number of type variables in scope (`LDomain`).
   Its laws (`LDomain.Lawful`) also require that duplicability and entailment are stable under
   weakening by new type variables (`dup_wk`, `entails_wk`). This is the usual stability of
   entailment under renaming. `freeLDomain_lawful` and `predLDomain_lawful` show these laws
   are satisfiable.
5. **Atomic constraints** are a predicate symbol applied to a list of types (`Atom P k`). The
   constraint of an existential type `∃ā. τ ⇐ Q` is stored as a finite family of scaled atoms,
   because inductive types cannot be nested inside the quotient types used for simple
   constraints. `exqC` turns this family into a simple constraint.
6. **Core calculus.** The core types are instantiated by (translations of) source types. The
   evidence `⟦Q⟧` for constraints is manipulated through a small set of primitive operations:
   coercion along entailment, split/join of `⊗`, discarding `ε`, and making `ω·Q`
   unrestricted (`Prim`). This is the role that the paper's (implicit) evidence
   representation plays. A scheme with no constraint is translated without an evidence
   argument.
7. **Data types** are given by a signature (`DataSig`) with type parameters. There are no
   separate base types: they are data types with 0 parameters. For a data type with no
   constructors, the empty `&`-combination of alternatives in constraint generation is taken
   to be `ε`.
8. Constraint generation reads a typing derivation that ignores constraints. The types and
   the instantiations of schemes are given, as provided by the paper's external
   type-inference oracle.
