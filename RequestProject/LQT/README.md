# Linearly Qualified Types — Lean formalization

This directory formalizes the paper *Linearly Qualified Types* (`linear-constraints.tex`,
typing rules in `ott.tex`; the Typst version `2103.06127v3.typ` has the same structure and
numbering and was also checked against the formalization): the qualified type system with linear constraints, constraint
generation, the constraint solver, and the desugaring into a linear core calculus.
Type polymorphism is included (`∀ā` in type schemes and `∃ā` in existential types).
The entry point is `RequestProject/LQT.lean`, which imports everything; the files are grouped
into one directory per section of the paper (see "Files" below). All results build
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
Sections 1, 4, 8, 9, 10 of the paper (introduction, applications, implementation in GHC,
related work, conclusion) contain no formal material; of §3 (examples), the examples of §3.1
and §3.2 are formalized in `Ch3_LinearConstraints/`.  See "What is not formalized, and why" below.

| Paper | Lean file | Main declarations |
|---|---|---|
| §2.1 "Multiplicities" | `Ch2_Background/Multiplicities.lean` | `Mult` |
| §3.1 "Minimal Examples": the setting | `Ch3_LinearConstraints/ExampleSetting.lean` | `exSig`, `exΓ`, `exD`, `givenC` |
| §3.1 "Minimal Examples" (Dithering, Neglecting, Overusing, `notNeglecting`) | `Ch3_LinearConstraints/MinimalExamples.lean` | `notNeglecting_typed`, `notNeglecting_inferred`, `notNeglecting_typed_by_inference`, `neglecting_rejected`, `overusing_rejected`, `dithering_rejected` |
| §3.2 "Restricting to a linear context with `Linearly`" (`bad`, `badToo`, two arrays from one `Linearly`) | `Ch3_LinearConstraints/Linearly.lean` | `badToo_rejected`, `badToo_not_inferred`, `twoArrays_typed`, `twoArrays_inferred`, `bad_not_inferred`, `bad_omega_typed` |
| §5.1, Definition 5.1 "Atomic constraints" | `Ch5_QualifiedTypeSystem/Syntax.lean` | `Atom` |
| §5.1, Definition 5.2 "Simple constraints" | `Ch5_QualifiedTypeSystem/SimpleConstraints.lean` | `SConstr`, `SConstr.atom` |
| §5.1, scaling `π·Q` (before Lemma 5.4) | `Ch5_QualifiedTypeSystem/SimpleConstraints.lean` | `SConstr.smul` |
| §5.1, Definition 5.3 "Entailment relation" | `Ch5_QualifiedTypeSystem/Entailment.lean`, `Ch5_QualifiedTypeSystem/SimpleConstraints.lean` | `Domain`, `SConstr.InDup` |
| §5.1, Figure 4 "Requirements for the entailment relation" | `Ch5_QualifiedTypeSystem/Entailment.lean` | `Domain.CommonLaws`, `Domain.PaperLaws`, `Domain.Lawful` |
| §5.1, Lemma 5.4 "Scaling" | `Ch5_QualifiedTypeSystem/EntailmentLemmas.lean` | `Domain.Lawful.scaling` |
| §5.1, Lemma 5.5 "Inversion of scaling" | `Ch5_QualifiedTypeSystem/EntailmentLemmas.lean` | `Domain.Lawful.scaling_inv`, `Domain.PaperLaws.scaling_inv` |
| §5.1, Corollary 5.6 "Linear assumptions" | `Ch5_QualifiedTypeSystem/EntailmentLemmas.lean` | `Domain.Lawful.linear_assumptions`, `Domain.PaperLaws.linear_assumptions` |
| §5.1, remark after Figure 4: `1·q ⊩ ω·q` is prohibited even for `q ∈ 𝒟` | `Ch5_QualifiedTypeSystem/EntailmentLemmas.lean`, `Ch6_ConstraintInference/FreeDomain.lean` | `Domain.Lawful.one_entails_omega`, `freeDomain_not_one_entails_omega` |
| §5.2, Figure 5 "Grammar of the qualified type system" | `Ch5_QualifiedTypeSystem/Syntax.lean` | `Ty`, `Scheme`, `DataSig`, `Tm` |
| §5.2, Figure 6 "Qualified type system" | `Ch5_QualifiedTypeSystem/Typing.lean` | `HasType` |
| §5.2, paragraph "Linear functions" (`f x` with `f : a →ω b` / `f : a →1 b` and `x : 1·q ⇒ a`) | `Ch5_QualifiedTypeSystem/LinearFunctions.lean` | `unrestrictedFun_rejected`, `linearFun_typed` |
| §6.1 "Wanted constraints" (grammar, scaling) | `Ch6_ConstraintInference/Wanted.lean` | `Wanted`, `Wanted.smul` |
| §6.1, Figure 7 "Wanted-constraint entailment" | `Ch6_ConstraintInference/Wanted.lean` | `LDomain.WEntails` |
| §6.1, Lemma 6.1 "Inversion" | `Ch6_ConstraintInference/WantedLemmas.lean` | `LDomain.Lawful.inv_tensor`, `inv_amp`, `inv_impl`, `LDomain.PaperLaws.inv_impl` |
| §6.1, Lemma 6.2 "Scaling" | `Ch6_ConstraintInference/WantedLemmas.lean` | `LDomain.Lawful.wentails_scaling` |
| §6.1, Lemma 6.3 "Inversion of scaling" | `Ch6_ConstraintInference/WantedLemmas.lean` | `LDomain.Lawful.wentails_scaling_inv`, `LDomain.PaperLaws.wentails_scaling_inv` |
| §6.1, remark: with a linear `C`, `C & C` is provable but `C ⊗ C` is not | `Ch6_ConstraintInference/WantedExamples.lean` | `with_entailed`, `tensor_not_entailed` |
| §6.2, Figure 8 "Constraint generation" | `Ch6_ConstraintInference/Generation.lean` | `Gen`, `withAll` |
| §6.2, Lemma 6.4 "Soundness of constraint generation" | `Ch6_ConstraintInference/Generation.lean` | `LDomain.Lawful.gen_sound` |
| ott source only: rule G_LetGen (`let`-generalisation; not in Figure 8, discussed in a commented-out section of the paper) | `Ch6_ConstraintInference/GenLetGen.lean` | `GenG`, `Gen.toGenG`, `LDomain.Lawful.genG_sound` |
| §6.3, atomic-solver judgement | `Ch6_ConstraintInference/Solver.lean` | `AtomSolver` |
| §6.3, Lemma 6.5 "Constraint solver soundness" | `Ch6_ConstraintInference/Solver.lean` | `LDomain.Lawful.solve_sound`, `solve_sound_strong` |
| §6.3, Property 6.6 "Atomic-constraint solver soundness" | `Ch6_ConstraintInference/Solver.lean` | `AtomSolver.PaperSound` (and the stronger `AtomSolver.Sound`) |
| §6.3.1, Figure 9 "Constraint solver" | `Ch6_ConstraintInference/Solver.lean` | `Solve` |
| §6.3.2, Figure 10a "Entailment relation" | `Ch6_ConstraintInference/FreeDomain.lean` | `freeEntails`, `freeDomain`, `fig10a_*` |
| §6.3.2, Figure 10b "Atomic-constraint solver" | `Ch6_ConstraintInference/AtomicSolver.lean` | `simpleSolver`, `simpleSolver_sound` |
| §6.3.2, "the solver of Figure 10b is deterministic ... does not guess" | `Ch6_ConstraintInference/AtomicSolverProps.lean` | `simpleSolve`, `simpleSolver_iff_simpleSolve`, `simpleSolver_deterministic`, `simpleSolver_nondeterministic_without_invariant` |
| §6.3.2, incompleteness of the solver (`ambiguous1`) | `Ch6_ConstraintInference/SolverIncompleteness.lean` | `ambiguousW`, `ambiguous_entailed`, `ambiguous_not_solved` |
| §7.1, Figure 11 "Core calculus (subset)"; App. A.1, Figures 13 and 14 | `Ch7_Desugaring/CoreCalculus.lean` | `CTy`, `CScheme`, `CTm`, `CHasType` |
| §7.2.1 "Evidence", Figure 12a "Evidence passing" | `Ch7_Desugaring/CoreCalculus.lean` | `CTy.ev`, `Prim`, `PrimTy` |
| §7.2.2 "Translating types" | `Ch7_Desugaring/CoreCalculus.lean` | `Ty.ds`, `Scheme.ds` |
| §7.2.3 "Translating terms", Figure 12b; App. A.2, Figure 15 "Desugaring" | `Ch7_Desugaring/Desugar.lean` | `desugarAt`, `desugar`, `dsLet`, `dsLetSig` |
| §7.2.3, Theorem 7.1 "Desugaring" | `Ch7_Desugaring/DesugarTyping.lean` | `desugar_typed` (induction: `desugarAt_typed`) |
| App. B.5, Lemma B.1 (`π·(ρ·Q) = (π⋅ρ)·Q`) | `Ch5_QualifiedTypeSystem/SimpleConstraints.lean` | `mul_smul` field of the `DistribMulAction Mult (SConstr A)` instance |
| App. B.6, Lemma B.2 "`𝒟` discarding" | `Ch5_QualifiedTypeSystem/Entailment.lean` | `Domain.Lawful.discard_dup`, `weaken_dup` |
| App. B.6, Lemma B.3 "`𝒟` duplication" | `Ch5_QualifiedTypeSystem/Entailment.lean` | `Domain.Lawful.dup_dup`, `dup_contraction` |
| App. B.6, Lemma B.4 "Transitive tensor decomposition" | `Ch5_QualifiedTypeSystem/EntailmentLemmas.lean` | `Domain.Lawful.transitive_tensor_decomposition` |
| App. B.6, Lemma B.5 "Weakening of wanteds" | `Ch6_ConstraintInference/WantedLemmas.lean` | `LDomain.Lawful.wentails_weaken` |
| App. B.6, Lemma B.6 (`π·(ρ·C) = (π⋅ρ)·C`) | `Ch6_ConstraintInference/Wanted.lean` | `Wanted.smul_smul` |

Files with no counterpart in the paper: everything in `Infrastructure/` (`Usage.lean`,
`UsageVec.lean`, `Map.lean`), and `Ch5_QualifiedTypeSystem/LeveledDomains.lean`, `Ch5_QualifiedTypeSystem/TypingInv.lean`,
`Ch6_ConstraintInference/GenerationInv.lean`, `Ch6_ConstraintInference/FreeLDomain.lean`, `Ch7_Desugaring/DesugarTypingAux.lean`.

### What is not formalized, and why

* **Definition 2.1 "Consume exactly once"** (§2) is a statement about the run-time behaviour of
  programs; the paper gives no operational semantics for its languages, so there is nothing
  formal to state it about.
* **§4 (capabilities, arrays, borrowing, slices, quicksort), Figures 1–3, and the
  `read2AndDiscard` example of §1** are Haskell programs and library interfaces illustrating the
  design; they use features outside the formal language (type classes, `IO`, type-level
  indices, records of capabilities).  The small programs of §3.1 and §3.2 are formalized
  (`Ch3_LinearConstraints/MinimalExamples.lean`, `Ch3_LinearConstraints/Linearly.lean`); `linearly :: (Linearly ⊸ Ur r) ⊸ Ur r` itself is
  higher-rank (a qualified type as an argument) and is not expressible in the formal language,
  so the `Linearly` examples start from the given linear assumption `1·𝓛` it provides.
* **The examples `f = linearly $ ...` (choice of the most recent `RW n`) and `ambiguous2` of
  §6.3.2** are about which copy of a constraint is consumed (its run-time evidence), which the
  provability-level judgements cannot distinguish; `ambiguous1` is formalized at the level of its
  wanted constraint (see deviation 10).
* **§8 (implementation in GHC, superclasses, equality constraints, inferring pack/unpack),
  §9, §10** contain no formal statements.
* **Rule C_Top (`Q ⊢ ⊤`)** appears in the ott source but, like the paper (which explains in a
  commented-out section that it is left out because of the non-determinism it causes in the
  solver), we do not include `⊤`: the constraint of an empty `case` is `ε` (deviation 7).

## Files

The directories follow the sections of the paper.  Sections 1 and 4 (introduction, memory
ownership API) and 8–10 have no formal content and so no directory.  The material of
Appendix A (full core calculus and desugaring) lives with §7, and each proof of Appendix B
lives with the lemma it proves.  All declarations are in the namespace `LQT` (the examples in
`LQT.Examples`), whatever their directory.

| File | Content (paper section) |
|---|---|
| **`Ch2_Background/`** | **§2 "Background: Linear Haskell"** |
| `Multiplicities.lean` | multiplicities `1`, `ω` and their product (§2.1) |
| **`Ch3_LinearConstraints/`** | **§3 "Working with linear constraints"** |
| `ExampleSetting.lean` | the setting of the examples (constraint `C`, `useC`, `const`, data types); reused by later examples |
| `MinimalExamples.lean` | the minimal examples of §3.1: one accepted (also by the inference algorithm), three rejected |
| `Linearly.lean` | the `Linearly` examples of §3.2 (`bad`, `badToo`, two arrays) |
| **`Ch5_QualifiedTypeSystem/`** | **§5 "A qualified type system for linear constraints"** |
| `SimpleConstraints.lean` | simple constraints `Q = (U, L)`, `ε`, `⊗`, scaling (§5.1 Def. 5.2, Lemma B.1) |
| `Entailment.lean` | constraint domains, the laws of Fig. 4 and the repaired laws, Lemmas B.2, B.3 |
| `EntailmentLemmas.lean` | Lemmas 5.4/5.5, Corollary 5.6, Lemma B.4, `1·q ⊮ ω·q` |
| `LeveledDomains.lean` | families of domains indexed by the number of type variables (not in the paper) |
| `Syntax.lean` | types, schemes, atoms, data signatures, expressions (Fig. 5, Def. 5.1) |
| `Typing.lean` | the qualified type system `Q ; Γ ⊢ e : τ` (Fig. 6) |
| `TypingInv.lean` | inversion lemmas for the typing rules (below chains of E_Sub) |
| `LinearFunctions.lean` | the *Linear functions* example of §5.2 |
| **`Ch6_ConstraintInference/`** | **§6 "Constraint inference"** |
| `Wanted.lean` | wanted constraints `C`, their scaling, `Q ⊢ C` (Fig. 7), Lemma B.6 |
| `WantedLemmas.lean` | Lemmas 6.1–6.3, B.5 |
| `WantedExamples.lean` | `C & C` vs `C ⊗ C` (remark of §6.1) |
| `Generation.lean` | constraint generation (Fig. 8), **Lemma 6.4** (`gen_sound`) |
| `GenerationInv.lean` | inversion lemmas for constraint generation |
| `GenLetGen.lean` | constraint generation extended with rule G_LetGen of the ott source, and its soundness (`genG_sound`) |
| `Solver.lean` | constraint solver (Fig. 9), **Lemma 6.5** (`solve_sound`), Property 6.6, end-to-end `infer_sound` |
| `FreeDomain.lean` | the stripped-down domain of §6.3.2 / Fig. 10a; satisfiability of the laws |
| `FreeLDomain.lean` | lawful leveled domains exist (`freeLDomain_lawful`, `predLDomain_lawful`) |
| `AtomicSolver.lean` | the atomic solver of Fig. 10b and its soundness (`simpleSolver_sound`) |
| `AtomicSolverProps.lean` | the atomic solver of Fig. 10b as a deterministic function (§6.3.2) |
| `SolverIncompleteness.lean` | incompleteness of the solver (`ambiguous1`, §6.3.2) |
| **`Ch7_Desugaring/`** | **§7 "Desugaring"** (and Appendix A) |
| `CoreCalculus.lean` | linear core calculus (Fig. 11 / App. A.1, Figs. 13–14) with polymorphic `let` and existential pairs; evidence and translation of types (§7.2.1, §7.2.2) |
| `Desugar.lean` | desugaring `⟦d⟧_z` (Fig. 12b / App. A.2, Fig. 15) |
| `DesugarTypingAux.lean`, `DesugarTyping.lean` | **Theorem 7.1** (`desugar_typed`) |
| **`Infrastructure/`** | **no counterpart in the paper** |
| `Usage.lean` | the usage semiring `{0, 1, ω}` replacing named contexts |
| `UsageVec.lean` | usage-vector algebra for renamings |
| `Map.lean` | mapping over the atoms of a constraint (used for renaming/substitution) |

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
* `LQT.LDomain.Lawful.genG_sound`: constraint generation remains sound with rule G_LetGen.
* `LQT.Examples.*`: `notNeglecting` is typable and inferred, `neglecting`, `overusing` and
  `dithering` have no typing derivation (§3.1); the examples of §3.2 and §5.2
  (`Ch3_LinearConstraints/Linearly.lean`, `Ch5_QualifiedTypeSystem/LinearFunctions.lean`) and the
  remarks of §6.1 and §6.3.2 (`Ch6_ConstraintInference/WantedExamples.lean`,
  `Ch6_ConstraintInference/SolverIncompleteness.lean`).
* `LQT.simpleSolver_deterministic`: the atomic solver of Fig. 10b never has to guess.
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
8. **Solver rules for simple constraints.** Figure 9 only solves single atoms `π·q`; the paper
   implicitly treats a simple constraint as the `⊗` of its atoms.  We add two rules, S_Empty
   (`ε` consumes nothing) and S_Split (`Q₁ ⊗ Q₂` is solved like S_Mult), without which the
   solver could not solve the `ε` emitted for constructors and unqualified variables.  Lemma 6.5
   is proved for the extended solver.
9. Constraint generation reads a typing derivation that ignores constraints. The types and
   the instantiations of schemes are given, as provided by the paper's external
   type-inference oracle.
10. **Remarks of §6.3.2 and Figure 10b.**  Rule `Atom_OneD` is printed with conclusion
    `U ; D, 𝓛 ; L ⊢ 1·q ⇝ L` for an arbitrary `q`, which would be unsound; we read it with
    `q = 𝓛`.  The determinism of Figure 10b (`simpleSolver_iff_simpleSolve`) needs the invariant
    `𝓛 ∉ L` maintained by the solver of Figure 9 (without it, `Atom_OneL` and `Atom_OneD` both
    apply: `simpleSolver_nondeterministic_without_invariant`).  The type of `giveC` in the
    `ambiguous` examples is written `(C ⇒ Int) → Int`; with an unrestricted arrow the argument's
    implication is `ω·(ω·C ⊸ 1·C)` which cannot use the linear `C` at all, so `ambiguous1` would
    be ill-typed and `ambiguous2` would be solved.  The incompleteness the paper describes arises
    when `giveC`'s argument is used linearly, i.e. for the implication `1·(ω·C ⊸ 1·C)`, which is
    what `ambiguous_entailed` / `ambiguous_not_solved` formalize.
11. **§3.2, `bad`.**  The paper says `bad = let arr = new 5 in (arr, arr)` is rejected.  This
    holds for the inference algorithm (`bad_not_inferred`), but the declarative system of
    Figure 6 accepts the version with `π = ω` (`bad_omega_typed`): rule E_Let lets `arr` be given
    the qualified type `𝓛 ⇒ MArray`, so each use of `arr` re-runs `new 5` with its own copy of
    `𝓛` and no array is actually shared.
