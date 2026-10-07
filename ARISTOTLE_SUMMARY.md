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