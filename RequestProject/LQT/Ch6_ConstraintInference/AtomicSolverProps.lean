module

public import RequestProject.LQT.Ch6_ConstraintInference.AtomicSolver

/-!
# Determinism of the atomic-constraint solver of Figure 10b (§6.3.2)

Paper location: §6.3.2 "An atomic-constraint solver" (the claim that the solver of Figure 10b
"is deterministic: in all circumstances, only one of the rules can apply", so that it "does not
guess, thus never needs to backtrack").  The start and end of each part is marked by
`-- [PAPER ▶ START]` / `-- [PAPER ◀ END]` comments.

* `simpleSolve` is the solver of Figure 10b written as a function returning the output context
  (or `none` when no rule applies); `simpleSolver_iff_simpleSolve` shows that the rules of
  Figure 10b compute exactly this function, as long as the linear context `L` does not contain
  the duplicable `𝓛` (the solver of Figure 9 maintains this invariant: duplicable linear
  assumptions are put in `D`).  Hence the atomic solver is deterministic
  (`simpleSolver_deterministic`).  Without the invariant, `Atom_OneL` and `Atom_OneD` can both
  apply to `1·𝓛` with different outputs (`simpleSolver_nondeterministic_without_invariant`).
* `solve_simple_count`, `solve_simple_U`: helpers on the solver of Figure 9 instantiated with
  the solver of Figure 10b, used by the examples.
-/

@[expose] public section

namespace LQT

section
variable {A : Type*} [DecidableEq A]

-- [NOT IN PAPER ▶ START] list helper: removing the last occurrence of an element
/-- Removing the last occurrence of `q` from a list. -/
def eraseLast (q : A) (L : List A) : List A := (L.reverse.erase q).reverse

lemma eraseLast_append_cons {q : A} (L₁ L₂ : List A) (hq : q ∉ L₂) :
    eraseLast q (L₁ ++ q :: L₂) = L₁ ++ L₂ := by
  have : q ∉ L₂.reverse := by simpa using hq
  simp [eraseLast, List.erase_append_right _ this]

lemma exists_split_last {q : A} {L : List A} (h : q ∈ L) :
    ∃ L₁ L₂, L = L₁ ++ q :: L₂ ∧ q ∉ L₂ := by
  induction L with
  | nil => simp at h
  | cons a L ih =>
    by_cases hL : q ∈ L
    · obtain ⟨L₁, L₂, rfl, h₂⟩ := ih hL
      exact ⟨a :: L₁, L₂, rfl, h₂⟩
    · have : a = q := by
        rcases List.mem_cons.mp h with h | h
        · exact h.symm
        · exact absurd h hL
      exact ⟨[], L, by simp [this], hL⟩
-- [NOT IN PAPER ◀ END] list helper

-- [PAPER ▶ START] §6.3.2 › Figure 10b, "It is deterministic: in all circumstances, only one of the
--   rules can apply. This means that the algorithm does not guess, thus never needs to backtrack."
/-- The atomic-constraint solver of Figure 10b as a (deterministic) function: it returns the
output linear context `Lₒ`, or `none` when no rule applies. -/
def simpleSolve (l : A) (U : Finset A) (Dl Li : List A) : Mult → A → Option (List A)
  | .omega, q => if q ∈ U then some Li else none
  | .one, q =>
    if q ∈ U then (if q ∈ Dl ∨ q ∈ Li then none else some Li)
    else if q ∈ Li then some (eraseLast q Li)
    else if q = l ∧ Dl.getLast? = some l then some Li
    else none

/-- The rules of Figure 10b compute exactly the function `simpleSolve`, provided the linear
context `Lᵢ` does not contain the duplicable constraint `𝓛` (an invariant of the solver of
Figure 9, which puts duplicable linear assumptions in `D`). -/
theorem simpleSolver_iff_simpleSolve (l : A) {U : Finset A} {Dl Li : List A} {π : Mult} {q : A}
    {Lo : List A} (hl : l ∉ Li) :
    simpleSolver l U Dl Li π q Lo ↔ simpleSolve l U Dl Li π q = some Lo := by
  constructor
  · intro h
    cases h with
    | many hq => simp [simpleSolve, hq]
    | oneL L₁ L₂ hq₂ hqU => simp [simpleSolve, hqU, eraseLast_append_cons _ _ hq₂]
    | oneD hlU => simp [simpleSolve, hlU, hl]
    | oneU hq hn =>
      simp only [List.mem_append, not_or] at hn
      simp [simpleSolve, hq, hn.1, hn.2]
  · intro h
    cases π with
    | omega =>
      simp only [simpleSolve] at h
      split_ifs at h with hq
      cases h
      exact .many hq
    | one =>
      simp only [simpleSolve] at h
      split_ifs at h with hU hDL hLi hl'
      · cases h
        exact .oneU hU (by simpa [not_or] using hDL)
      · cases h
        obtain ⟨L₁, L₂, rfl, h₂⟩ := exists_split_last hLi
        rw [eraseLast_append_cons _ _ h₂]
        exact .oneL L₁ L₂ h₂ hU
      · cases h
        obtain ⟨rfl, hlast⟩ := hl'
        obtain ⟨Dl', rfl⟩ : ∃ Dl', Dl = Dl' ++ [q] := by
          rw [List.getLast?_eq_some_iff] at hlast
          exact hlast
        exact .oneD hU

/-- **The atomic-constraint solver of Figure 10b is deterministic**: for given inputs (with `𝓛`
not in the linear context) there is at most one output. -/
theorem simpleSolver_deterministic (l : A) {U : Finset A} {Dl Li : List A} {π : Mult} {q : A}
    {Lo₁ Lo₂ : List A} (hl : l ∉ Li) (h₁ : simpleSolver l U Dl Li π q Lo₁)
    (h₂ : simpleSolver l U Dl Li π q Lo₂) : Lo₁ = Lo₂ := by
  rw [simpleSolver_iff_simpleSolve l hl] at h₁ h₂
  exact Option.some_injective _ (h₁.symm.trans h₂)

omit [DecidableEq A] in
/-- The invariant `𝓛 ∉ Lᵢ` is needed: if `𝓛` occurs in the linear context `L` and also at the end
of `D`, rules `Atom_OneL` and `Atom_OneD` both solve `1·𝓛`, with different outputs. -/
theorem simpleSolver_nondeterministic_without_invariant (l : A) :
    simpleSolver l ∅ [l] [l] .one l [] ∧ simpleSolver l ∅ [l] [l] .one l [l] :=
  ⟨simpleSolver.oneL [] [] (by simp) (by simp),
    simpleSolver.oneD (Dl := []) (by simp)⟩
-- [PAPER ◀ END] §6.3.2 › determinism of Figure 10b

-- [NOT IN PAPER ▶ START] helper: the solver of Figure 10b never consumes a linear assumption that
--   is also available unrestrictedly
lemma simpleSolver_count {l : A} {U : Finset A} {Dl Li : List A} {π : Mult} {q : A}
    {Lo : List A} {c : A} (h : simpleSolver l U Dl Li π q Lo) (hc : c ∈ U) :
    Li.count c = Lo.count c := by
  cases h with
  | many => rfl
  | oneL L₁ L₂ _ hqU =>
    have hne : q ≠ c := fun e => hqU (e ▸ hc)
    simp [List.count_append, hne]
  | oneD => rfl
  | oneU => rfl
-- [NOT IN PAPER ◀ END] helper

end

section Leveled
variable {A : Nat → Type} [∀ k, DecidableEq (A k)] [Weakening A]

-- [NOT IN PAPER ▶ START] helper: solving a simple wanted constraint with the solver of Figure 10b
--   does not consume a linear assumption that is also available unrestrictedly
lemma solve_simple_count (D : LDomain A) (l c : (k : Nat) → A k) {k : Nat} {U : Finset (A k)}
    {Dl Li : List (A k)} {C : Wanted A k} {Lo : List (A k)}
    (h : Solve D (fun k => simpleSolver (l k)) U Dl Li C Lo) :
    ∀ Q, C = .simple Q → c k ∈ U → Li.count (c k) = Lo.count (c k) := by
  induction h with
  | atom h => intro _ _ hc; exact simpleSolver_count h hc
  | mult => intro _ hC; cases hC
  | add => intro _ hC; cases hC
  | implOne => intro _ hC; cases hC
  | implMany => intro _ hC; cases hC
  | empty => intro _ _ _; rfl
  | split _ _ ih₁ ih₂ =>
    intro _ _ hc
    exact (ih₁ _ rfl hc).trans (ih₂ _ rfl hc)
/-- Solving a simple wanted constraint with the solver of Figure 10b requires its unrestricted
atoms to be available unrestrictedly (only rule `Atom_Many` solves `ω·q`). -/
lemma solve_simple_U (D : LDomain A) (l : (k : Nat) → A k) {k : Nat} {U : Finset (A k)}
    {Dl Li : List (A k)} {C : Wanted A k} {Lo : List (A k)}
    (h : Solve D (fun k => simpleSolver (l k)) U Dl Li C Lo) :
    ∀ Q, C = .simple Q → Q.U ⊆ U := by
  induction h with
  | atom h =>
    intro _ hC
    cases hC
    cases h with
    | many hq => simpa using hq
    | oneL => simp
    | oneD => simp
    | oneU => simp
  | mult => intro _ hC; cases hC
  | add => intro _ hC; cases hC
  | implOne => intro _ hC; cases hC
  | implMany => intro _ hC; cases hC
  | empty => intro _ hC; cases hC; simp
  | split _ _ ih₁ ih₂ =>
    intro _ hC
    cases hC
    simp only [SConstr.add_U, Finset.union_subset_iff]
    exact ⟨ih₁ _ rfl, ih₂ _ rfl⟩
-- [NOT IN PAPER ◀ END] helper

end Leveled

end LQT
