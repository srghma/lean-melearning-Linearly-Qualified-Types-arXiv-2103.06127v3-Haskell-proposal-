# Summary of changes for run 3376555f-79c8-41da-9447-665460a21f79
As you asked, I wrote the corrections to the paper in a separate document, `CORRECTIONS.md`, at the root of the project. The paper sources themselves (`linear-constraints.tex`, `2103.06127v3.typ`, `ott.tex`) are unchanged. `RequestProject.LQT` builds with no `sorry`, and the new theorems use only the standard axioms (`propext`, `Classical.choice`, `Quot.sound`).

**What `CORRECTIONS.md` contains.** For each problem it gives the location in the `.tex` (approximate line numbers), what goes wrong, the Lean results that back it, and replacement wording.
1. **Figure 1b, the type of `new`.** Unpacking binds the array linearly, so it can't then be passed to `free`, `read` or `write`, which take it unrestricted. Fix: `new :: Linearly =⚬ Int -> ∃ n. Ur (UArray a n) ⧀ RW n`, and the same change for `newRef` in §4.1. Two new sentences are proposed for §3.
2. **Figure 3, `pack pivotIdx`.** This binds `pivotIdx` linearly, and it is then passed to the unrestricted `Int` argument of `split`. Fix: `partition` and `go` return `Ur Int`, and `sort` uses `pack (Ur pivotIdx)`. A sentence for the text is included.
3. **§6.3.2, S_ImplOne vs Atom_OneL.** The text says S_ImplOne adds new hypotheses "on the front", but Atom_OneL as printed consumes the *last* occurrence. Two consistent fixes are given; the formalization uses option A (append at the end).
4. Other discrepancies, with proposed wording for each:
   - Figure 4, law (7), forces the set of duplicable constraints to be empty.
   - Lemma 5.5 is false once that set is non-empty.
   - Atom_OneD as printed solves any `1·q`, which is unsound.
   - Figure 9 has no rule for `ε` or for a tensor of atoms.
   - `bad` is accepted by the declarative type system.
   - The arrow in `giveC`'s type should be linear.

**New Lean proofs** (`RequestProject/LQT/Ch4_MemoryOwnership/PrintedCode.lean`). Until now, items 1 and 2 were argued only in prose. These theorems prove that the code as printed has no typing derivation in the system of Figure 6, for every given constraint, type and usage. Because inference is sound, the inference algorithm rejects it too.
- `unpack_then_unrestricted_rejected`: the general fact. `let pack x = e₁ in f x` is ill typed whenever `f` takes its argument unrestricted.
- `free_after_unpack_rejected`: `let pack arr = e in free arr` is ill typed for every expression `e`, so in particular for `new 10` at Figure 1b's type.
- `sort_printed_rejected`: Figure 3's `let pack pivotIdx = partition arr; pack (Ur (l, r)) = split arr pivotIdx in …` is ill typed, whatever stands in place of `partition arr` and whatever the rest of `sort` is.

The corrected programs were already shown to be accepted (`fLinearly_inferred`, `sort_inferred`, among others).

The new file is imported from `RequestProject/LQT.lean`. `RequestProject/LQT/README.md` links to `CORRECTIONS.md`, and the three theorems are in the Properties table, marked proved.

# Summary of changes for run d6ad55dc-f047-4765-b608-bf5b9e042591
The items left open last time are now formalized, except the run-time content noted below. Everything uses de Bruijn indices for both term and type variables. `lake build RequestProject.LQT` succeeds with no `sorry`, and the new theorems use only the axioms `propext`, `Classical.choice` and `Quot.sound`.

**Definition 2.1, "Consume exactly once"** (`Ch2_Background/ConsumeExactlyOnce.lean`). The paper gives no operational semantics, so the run-time statement itself can't be formalized. Instead I formalized the definition's clauses as a syntactic predicate `Consumes Γ x τ e` in the core calculus (evaluate a base value; apply a function to one argument and consume the result; pattern-match a pair and consume both parts; pattern-match `Ur`). Proved:
- `Consumes.typed`: every such consumer is well typed and uses `x` exactly once, and no other variable linearly.
- `linear_arrow_meaning`: if `f : τ₁ ⊸ τ₂` and `f y` is consumed exactly once, then `y` is used exactly once. With an unrestricted arrow, `y` is used with multiplicity ω (`unrestricted_arrow_meaning`).

**§1, §3.2, §4 and Figures 1–3** (`Ch4_MemoryOwnership/`). `Setting.lean` writes the APIs of Figure 1b, `linearly`, references, `split`/`join`/`lendMut` and the quicksort signatures as a context `memΓ`. `Infers` means "accepted by constraint generation (Figure 8) followed by the solver (Figures 9/10b)". `Infers.typed` turns that into a typing derivation in Figure 6. These programs are accepted, each with a `_typed` corollary:
- `read2AndDiscard_inferred` (§1)
- `swap_inferred` (Figure 2)
- `sort_inferred`, `partition_inferred`, `go_inferred` (Figure 3)
- `twoArraysLinearly_inferred`: two arrays allocated inside the `linearly` primitive (§3.2)
- `fLinearly_inferred`: the `f = linearly $ …` example (§6.3.2)
- `refExample_inferred`: a small program using the §4.1 reference API (my own example; the paper gives none)

**Encodings and deviations** (all documented in the README):
- **Qualified argument types:** `linearly`'s argument `Q =⚬ τ` is passed as a linear function from evidence `∃. () ⇐ Q`, which the continuation unpacks.
- **`lendMut`:** its scoped continuation is replaced by a direct-style version plus `unlendMut`.
- **Recursion:** recursive definitions are checked against their signature in the context, and `go` is lambda-lifted.
- **Return types:** I changed some return types because the paper's own code doesn't type-check as printed. A variable bound by `pack` is linear, but it is then passed to an unrestricted argument.
  - `new` and `newRef` return `Ur …`, matching the paper's code `pack (Ur arr) = new 10`; Figure 1b's type doesn't have the `Ur`.
  - `partition` and `go` return `Ur Int`, because Figure 3 passes the linear `pivotIdx` to `split`.

**Which copy of a constraint is used (`f`).** `simpleSolve_most_recent` proves the atomic solver consumes the local copy of a constraint and leaves the outer copies alone. For this to hold, an earlier change in this session makes rule S_ImplOne add local hypotheses at the end of the list. That's the end rule Atom_OneL takes from as printed, although the paper says S_ImplOne adds them "on the front".

**`ambiguous2`** (`SolverIncompleteness.lean`). `ambiguous2_entailed` and `ambiguous2_not_solved` show its wanted constraint is provable from a linear `C`, but the solver can't solve it. Like the existing `ambiguous1` result, this is stated at the level of the generated wanted constraint.

**Still not formalized:** `lend`, the plain Linear Haskell API of Figure 1a, and rejection examples in the memory setting. Rejection examples remain in `Ch3_LinearConstraints/`.

The README, the imports in `RequestProject/LQT.lean` and the Properties table are updated.

## Suggested follow-up

Possible inconsistencies in the paper (each documented in the README):
- **Figure 1b vs §6.3.2:** Figure 1b gives `new` the type `∃ n. UArray a n ⧀ RW n`, but the code in §6.3.2 uses `pack (Ur arr) = new 10`. With Figure 1b's type, the linear `arr` couldn't be passed to `free`.
- **Figure 3:** `pack pivotIdx = partition arr` binds `pivotIdx` linearly, then passes it to the unrestricted `Int` argument of `split`.
- **S_ImplOne vs Atom_OneL:** S_ImplOne says new hypotheses go on the front of the list, while Atom_OneL as printed consumes the last occurrence.

I can draft wording for corrections if that would help.

# Summary of changes for run dfd2ee0a-dbeb-4f04-aeb5-4acc16ca59ce
I moved the formalization into one directory per section of the paper and split the files that covered more than one topic. No definition, statement or proof was changed; only which file each lives in. `RequestProject.LQT` and the default target build with no `sorry`. I re-checked the axioms of the main results (`desugar_typed`, `genG_sound`, `ambiguous_not_solved`, `bad_omega_typed`, `one_entails_omega`): they use only `propext`, `Classical.choice` and `Quot.sound`.

**New layout** under `RequestProject/LQT/`:
- **`Ch2_Background/`**: `Multiplicities.lean` (§2.1).
- **`Ch3_LinearConstraints/`**:
  - `ExampleSetting.lean`: the shared setting of the examples (constraint `C`, `useC`, `const`, the data types, the domain), reused by the later example files.
  - `MinimalExamples.lean` (§3.1).
  - `Linearly.lean` (§3.2).
- **`Ch5_QualifiedTypeSystem/`**:
  - `SimpleConstraints.lean` (Definition 5.2, Lemma B.1).
  - `Entailment.lean` (Definition 5.3, Figure 4, Lemmas B.2 and B.3).
  - `EntailmentLemmas.lean` (Lemmas 5.4 and 5.5, Corollary 5.6, Lemma B.4, the \(1\cdot q \nVdash \omega\cdot q\) remark).
  - `LeveledDomains.lean`, `Syntax.lean`, `Typing.lean`, `TypingInv.lean`, `LinearFunctions.lean` (the §5.2 example).
- **`Ch6_ConstraintInference/`**:
  - Wanted constraints: `Wanted.lean` (grammar, Figure 7, Lemma B.6), `WantedLemmas.lean` (Lemmas 6.1–6.3, B.5), `WantedExamples.lean` (the §6.1 remark about `C ⊗ C` and `C & C`).
  - Generation: `Generation.lean`, `GenerationInv.lean`, `GenLetGen.lean`.
  - Solving: `Solver.lean` (Figure 9, Lemma 6.5), `AtomicSolver.lean` (Figure 10b), `AtomicSolverProps.lean` (determinism), `SolverIncompleteness.lean`.
  - Domains: `FreeDomain.lean` (Figure 10a), `FreeLDomain.lean`.
- **`Ch7_Desugaring/`**: `CoreCalculus.lean`, `Desugar.lean`, `DesugarTypingAux.lean`, `DesugarTyping.lean`. Appendix A material sits here with the figures it completes.
- **`Infrastructure/`** (no counterpart in the paper): `Usage.lean`, `UsageVec.lean`, `Map.lean`.

Sections 1, 4 and 8–10 have no formal content, so they have no directory. Each Appendix B proof stays next to the lemma it proves.

**What was split or moved, and why**
- The old `Basic.lean` became multiplicities (Chapter 2), usages (Infrastructure) and simple constraints (Chapter 5).
- `Entailment.lean`, `Wanted.lean` and `Solver.lean` were each split into a definitions file and a lemmas file.
- The two mixed example files were split by the paper section each example comes from.
- The type-variable-level machinery (`Weakening`, `LDomain`, `LDomain.Lawful`) moved out of the §6.1 file into `LeveledDomains.lean`. Before, the §5 syntax had to import the §6 wanted-constraint file just to get it; now it doesn't.
- The general inversion lemmas for constraint generation moved from an example file to `GenerationInv.lean`. As a result, their names lost the `Examples` namespace prefix. They are helpers, not registered results. Every other declaration keeps its fully qualified name (`LQT…`, with the examples under `LQT.Examples`).

**Other updates**
- Every file has a header giving its paper location, and the `[PAPER ▶ START]` / `[PAPER ◀ END]` markers are still balanced in every file.
- `RequestProject/LQT.lean` imports everything, grouped by chapter.
- `RequestProject/LQT/README.md` has the new paths in its paper-to-Lean table and a per-directory file list.
- In the Properties table, every entry now points to its new file. Statuses are unchanged.

# Summary of changes for run edc5bbf1-3632-484c-8a64-8bb01d181821
I checked `2103.06127v3.typ` against the existing formalization. It has the same sections, figures and lemma numbering as the `.tex` source, and every numbered definition, figure, lemma and theorem was already formalized. What was missing were the smaller formal claims the paper makes in its running text. I formalized those that the formal language can express. `RequestProject.LQT` builds, there is no `sorry`, and the new theorems use only the standard axioms (`propext`, `Classical.choice`, `Quot.sound`).

**New file `RequestProject/LQT/SolverProps.lean`**
- **§6.3.2, "the solver of Figure 10b is deterministic, it does not guess":** `simpleSolve` writes the solver as a function. `simpleSolver_iff_simpleSolve` shows the rules compute exactly that function, so `simpleSolver_deterministic` follows (at most one output). This needs the condition that `Linearly` is not in the linear context; the solver of Figure 9 always keeps it that way. Without it, two rules can both fire with different results (`simpleSolver_nondeterministic_without_invariant`).
- **§6.3.2, the solver is incomplete (`ambiguous1`):** for the wanted constraint \(1\cdot(\omega\cdot C \multimap 1\cdot C)\), a single linear \(C\) entails it (`ambiguous_entailed`), but the solver cannot solve it (`ambiguous_not_solved`).
- **§6.1:** with one linear \(C\), \(C \mathbin{\&} C\) is provable (`with_entailed`) and \(C \otimes C\) is not (`tensor_not_entailed`).
- **§5.1, "\(1\cdot q \Vdash \omega\cdot q\) is prohibited":** in every lawful domain it implies \(\varepsilon \Vdash 1\cdot q\) (`Domain.Lawful.one_entails_omega`). In the domain of Figure 10a it never holds (`freeDomain_not_one_entails_omega`).

**New file `RequestProject/LQT/ExamplesMore.lean`**
- **§5.2, "Linear functions":** `f x` with `f : Int →ω Int` and `x : 1·C ⇒ Int` cannot be typed from a linear `C` (`unrestrictedFun_rejected`). With a linear `f` it can (`linearFun_typed`).
- **§3.2, the `Linearly` examples**, using `new :: Linearly ⊸ Int → MArray`:
  - `badToo = Ur (new 5)` is rejected by the type system (`badToo_rejected`) and by inference (`badToo_not_inferred`).
  - Creating two arrays from one linear `Linearly` is accepted by the type system (`twoArrays_typed`) and by inference (`twoArrays_inferred`).
  - `bad = let arr = new 5 in (arr, arr)` is rejected by inference for both multiplicities of `let` (`bad_not_inferred`).

**Discrepancies with the paper's text** (also listed as items 10–11 under deviations in `RequestProject/LQT/README.md`)
- **`bad` is accepted by the declarative type system** when `arr` is unrestricted (`bad_omega_typed`). Rule E_Let lets `arr` require its own `Linearly`, so each use re-runs `new 5` and no array is shared. The paper's claim that `bad` is rejected therefore holds only for the inference algorithm.
- **Rule `Atom_OneD` in Figure 10b** is printed as solving any `1·q`, which would be unsound. I read it as solving only `1·Linearly`.
- **The `ambiguous` examples** use `giveC :: (C ⇒ Int) -> Int`. With that unrestricted arrow, `ambiguous1` is ill-typed and the solver actually accepts `ambiguous2`. The incompleteness the paper describes only appears if `giveC` uses its argument linearly, and that is the version I formalized.

**Still not formalized:** Definition 2.1 (it describes run-time behaviour, and the paper gives no operational semantics); §4 and Figures 1–3; the `linearly` primitive itself, whose argument has a qualified type the formal language can't express, so the §3.2 examples start from the linear `Linearly` it would provide; and the `f = linearly $ …` and `ambiguous2` discussions, which concern which copy of a constraint gets used, not whether it is provable.

The README's coverage table and file list are updated. All 9 new results are in the Properties table and marked proved.

# Summary of changes for run f3c51315-89e0-43b5-9c86-39322e116f9c
**Short answer:** almost. The previous runs had already formalized every definition, figure, lemma and theorem the paper presents: Figures 4–15, Lemmas 5.4–6.5, Property 6.6, Theorem 7.1 and the appendix lemmas B.1–B.6. Checking the paper and `ott.tex` against the Lean code turned up three gaps, plus some material that can't be formalized. I filled the three gaps. `RequestProject.LQT` builds with no `sorry`, and the new theorems use only the standard axioms (`propext`, `Classical.choice`, `Quot.sound`).

**What I added**

1. **The constraint solver couldn't handle the empty constraint `ε`.** Figure 9 only solves single atoms `π·q`; the paper silently treats a simple constraint as the `⊗` of its atoms. Constraint generation emits `ε` for every data constructor and every variable without a constraint in its type. So, before this fix, the end-to-end theorem `infer_sound` could not be applied to essentially any real program. I added two rules to `Solve` in `Solver.lean`:
   - **S_Empty:** `ε` uses up no assumptions.
   - **S_Split:** `Q₁ ⊗ Q₂` is solved the same way S_Mult solves `C₁ ⊗ C₂`.
   
   Lemma 6.5 (both forms) is re-proved for the extended solver.

2. **Rule G_LetGen** (let-generalisation). It is in `ott.tex` but not shown in Figure 8. The new file `GenLetGen.lean` defines constraint generation extended with this rule (`GenG`), shows every Figure 8 derivation is still a derivation there (`Gen.toGenG`), and proves soundness, `genG_sound` (the counterpart of Lemma 6.4). The proof relies on rule E_Let, which lets a `let`-bound variable carry a constraint.

3. **The minimal examples of §3.1** (`Examples.lean`). They are written in the formal language with a linear constraint `C`, `useC :: C ⊸ Int` and the linear `const :: a ⊸ b → a`, using the simplified constraint domain of §6.3.2 with nothing duplicable. `10` is modelled as a constructor of `Int` with no arguments.
   - `notNeglecting_typed`: `const useC 10` type-checks at `Int`.
   - `notNeglecting_inferred` / `notNeglecting_typed_by_inference`: the inference algorithm accepts it too (constraint generation, then the solver with the atomic solver of Figure 10b). This relies on S_Empty.
   - `neglecting_rejected`, `overusing_rejected`, `dithering_rejected`: these three programs have no typing derivation at any type, any usage of the context, and (for dithering) any multiplicity of the `case`.
   
   The proofs use new inversion lemmas for the typing rules (`TypingInv.lean`) and a counting argument: in this domain, entailment preserves the number of linear copies of `C`.

**Not formalized, and why** (also listed in `RequestProject/LQT/README.md`)
- **Definition 2.1 "Consume exactly once":** it is about run-time behaviour, and the paper gives no operational semantics to state it against.
- **§3.2, §4 and Figures 1–3:** Haskell APIs that use features outside the formal language (type classes, `IO`, type-level indices).
- **§8–§10:** these sections contain no formal statements.
- **Rule C_Top (`⊤`):** like the paper, which leaves it out because it makes the solver non-deterministic, it is not included. An empty `case` generates `ε` instead.

The new files are imported from `RequestProject/LQT.lean`. The README's coverage table, file list and list of deviations are updated, and the new results are in the Properties table.

# Summary of changes for run 91c72fbd-5d4b-41b2-a1ee-4f6d6303e981
I fixed the comments so they now refer to the paper (its sections, figures, definitions, lemmas and theorems) rather than slides. Only comments, docstrings, one section name and five theorem names changed; no definitions or proofs changed. The whole project still builds with no `sorry`.

**What the markers look like.** Each part of the paper now starts and ends with a pair of comments in the Lean files under `RequestProject/LQT/`:
```
-- [PAPER ▶ START] §6.2 › Lemma 6.4 "Soundness of constraint generation" (proof: Appendix B.6)
...
-- [PAPER ◀ END] §6.2 › Lemma 6.4
```
- **Coverage:** §2.1, Definitions 5.1–5.3, Figures 4–15, Lemmas 5.4/5.5, Corollary 5.6, Lemmas 6.1–6.5, Property 6.6, Theorem 7.1 and Lemmas B.1–B.6 are all marked.
- **Material not in the paper** (de Bruijn and renaming infrastructure, helper lemmas, the non-vacuity checks, the finding that the Figure 4 laws force `𝒟 = ∅`, and the end-to-end inference theorem) is marked the same way with `-- [NOT IN PAPER ▶ START]` / `-- [NOT IN PAPER ◀ END]`.
- **Typing rules:** the inductive definitions have one constructor per rule, already named in each docstring (E_*, G_*, S_*, C_*). Each case of the desugaring function is labelled with the typing rule it handles.
- **File headers:** each file's header now has a "Paper location" line, and every file has balanced START/END markers.
- **Overview:** `RequestProject/LQT/README.md` has a new section, "Where each part of the paper is formalized". It lists each paper element, its Lean file and its main declarations, and explains how to search for the markers.

**Numbering corrected.** The earlier comments used numbers that don't match the paper as typeset from the supplied `linear-constraints.tex`. I recounted from the source and corrected them everywhere: in the Lean comments, the README and the Properties table. The main changes:

| Before | Now |
|---|---|
| entailment laws, Fig. 3 | Fig. 4 |
| grammar and typing rules, Fig. 4 | Figs. 5 and 6 |
| wanted-constraint entailment, Fig. 5 | Fig. 7 |
| generation and solver, Fig. 6 | Figs. 8 and 9 |
| stripped-down domain, Fig. 7a/7b | Fig. 10a/10b |
| core calculus, Fig. 8 | Fig. 11, with App. A.1, Figs. 13–14 |
| desugaring, Fig. 9 | Fig. 12b, with App. A.2, Fig. 15 |
| Lemmas 5.1/5.2, Corollary 5.3 | Lemmas 5.4/5.5, Corollary 5.6 |
| solver soundness, Lemma 6.6 | Lemma 6.5 |
| atomic-solver property, Property 6.5 | Property 6.6 |
| Lemmas B.4/B.5/B.6/B.8/B.9 | Lemmas B.2/B.3/B.4/B.5/B.6 |

To match, the theorems `fig7a_*` are now `fig10a_*`. Every marker also gives the item's title, so if your PDF is a different version with other numbering, the parts can still be found by name.

`RequestProject.LQT` builds successfully.

# Summary of changes for run ce20cd37-3020-4193-b5d4-bad745752b5d


## Suggested follow-up

I reached this run’s time limit. Send “continue” to pick up where I left off.