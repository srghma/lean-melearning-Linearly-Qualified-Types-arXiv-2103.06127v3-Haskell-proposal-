module

public import RequestProject.LQT.Ch3_LinearConstraints.ExampleSetting
public import RequestProject.LQT.Ch6_ConstraintInference.AtomicSolverProps

/-!
# Incompleteness of the constraint solver (§6.3.2, `ambiguous1`)

Paper location: §6.3.2 "An atomic-constraint solver" (the claim that refusing to solve a linear
constraint which is assumed both unrestrictedly and linearly "introduces incompleteness with
respect to the entailment relation").  The example uses the setting of the §3.1 examples
(`Ch3_LinearConstraints/ExampleSetting.lean`).

* `ambiguous_entailed` / `ambiguous_not_solved`: the incompleteness example (`ambiguous1`), at the
  level of the generated wanted constraint.
* `ambiguous2_entailed` / `ambiguous2_not_solved`: the same for `ambiguous2 = (giveC useC, useC)`,
  which the qualified type system accepts (the first `useC` consuming the local unrestricted `C`,
  the second the linear one) but the solver rejects, since it would have to guess.
-/

@[expose] public section

namespace LQT

namespace Examples

-- [PAPER ▶ START] §6.3.2, incompleteness of the solver (`ambiguous1`): "no rule solves a linear
--   constraint if it appears both in the unrestricted and a linear context ... This introduces
--   incompleteness with respect to the entailment relation."

/-- The wanted constraint of `ambiguous1 = giveC useC`, where `giveC` passes an unrestricted
copy of `C` to its argument (`C ⇒ Int`) and `useC` consumes a linear `C`: the implication
`1·(ω·C ⊸ 1·C)`. -/
def ambiguousW : Wanted (Atom Unit) 0 :=
  .impl .one 0 (SConstr.atom .omega cAtom) (.simple givenC)

/-- The wanted constraint of `ambiguous1` is entailed by the given linear `C`: the inner `C` can
be proved by the outer linear assumption (and the local unrestricted one discarded). -/
theorem ambiguous_entailed : exD.WEntails givenC ambiguousW := by
  have h : exD.WEntails ((Mult.one : Mult) • givenC) ambiguousW := by
    refine .impl .one (.dom ?_ (.id _))
    show freeEntails _ _ _
    refine ⟨?_, ?_, ?_⟩
    · simp
    · intro q _
      have hw : Weakening.wk 0 (cAtom : Atom Unit 0) = cAtom := rfl
      simp [SConstr.wk, givenC, SConstr.atom, hw]
    · intro q hq
      simp at hq
  simpa using h

/-- ... but the solver of Figure 9, with the atomic solver of Figure 10b, cannot solve it from
the given linear `C` (consuming it), whatever the choice of the duplicable constraint `𝓛`. -/
theorem ambiguous_not_solved (l : (k : Nat) → Atom Unit k) :
    ¬ Solve exD (fun k => simpleSolver (l k)) ∅ [] [cAtom] ambiguousW [] := by
  intro h
  unfold ambiguousW at h
  cases h with
  | implOne l₀ hl₀ hin _ =>
    have hl₀' : l₀ = [] := by
      have : (l₀ : Multiset (Atom Unit 0)) = 0 := by rw [hl₀]; rfl
      simpa using this
    subst hl₀'
    have hw : Weakening.wk 0 (cAtom : Atom Unit 0) = cAtom := rfl
    have := solve_simple_count exD l (fun _ => cAtom) hin _ rfl (by simp [SConstr.atom])
    simp [hw] at this

-- [PAPER ◀ END] §6.3.2, incompleteness

-- [PAPER ▶ START] §6.3.2, `ambiguous2 = (giveC useC, useC)`: "It is possible to give a type
--   derivation to ambiguous2 in the qualified type system ... by making the first useC consume the
--   unrestricted C and the second useC consume the linear C. This assignment, however, would
--   require the constraint solver to guess"

/-- The wanted constraint of `ambiguous2 = (giveC useC, useC)`: the implication of
`giveC useC` (as in `ambiguousW`) next to the linear `C` wanted by the second `useC` (the pair
constructor has linear fields): `1·(ω·C ⊸ 1·C) ⊗ 1·C`. -/
def ambiguous2W : Wanted (Atom Unit) 0 :=
  .tensor ambiguousW (.simple givenC)

/-- The wanted constraint of `ambiguous2` is entailed by the given linear `C`: the first `useC`
consumes the local unrestricted `C`, the second one the linear `C`. -/
theorem ambiguous2_entailed : exD.WEntails givenC ambiguous2W := by
  have hsplit : (givenC : SConstr (Atom Unit 0)) = 0 + givenC := by simp
  rw [hsplit]
  refine .tensor ?_ (.id _)
  have h : exD.WEntails ((Mult.one : Mult) • (0 : SConstr (Atom Unit 0))) ambiguousW := by
    refine .impl .one (.dom ?_ (.id _))
    show freeEntails _ _ _
    refine ⟨?_, ?_, ?_⟩
    · simp [givenC]
    · intro q _
      have hw : Weakening.wk 0 (cAtom : Atom Unit 0) = cAtom := rfl
      refine ⟨by simp [SConstr.wk], fun hlt => ?_⟩
      simp only [givenC, SConstr.atom, Multiset.count_singleton] at *
      by_contra hne
      simp_all [SConstr.wk]
    · intro q hq
      simp at hq
  simpa using h

/-- The solver of Figure 9 with the atomic solver of Figure 10b, and no duplicable linear
assumption, never solves a simple wanted constraint containing a linear atom `c` that is
available both unrestrictedly and linearly (no rule of Figure 10b applies to it). -/
lemma solve_simple_stuck (l c : (k : Nat) → Atom Unit k) {k : Nat} {U : Finset (Atom Unit k)}
    {Dl Li : List (Atom Unit k)} {C : Wanted (Atom Unit) k} {Lo : List (Atom Unit k)}
    (h : Solve exD (fun k => simpleSolver (l k)) U Dl Li C Lo) :
    ∀ Q, C = .simple Q → Dl = [] → c k ∈ U → c k ∈ Li → c k ∉ Q.L := by
  induction h with
  | atom h =>
    intro Q hC hDl hcU hcL
    cases hC
    cases h with
    | many => simp [SConstr.atom]
    | oneL L₁ L₂ _ hqU =>
      intro hc
      simp only [SConstr.atom, Multiset.mem_singleton] at hc
      exact hqU (hc ▸ hcU)
    | oneD => simp at hDl
    | oneU _ hq =>
      intro hc
      simp only [SConstr.atom, Multiset.mem_singleton] at hc
      exact hq (List.mem_append_right _ (hc ▸ hcL))
  | mult => intro _ hC; cases hC
  | add => intro _ hC; cases hC
  | implOne => intro _ hC; cases hC
  | implMany => intro _ hC; cases hC
  | empty => intro _ hC _ _ _; cases hC; simp
  | @split k U Dl Li Lo' Lo Q₁ Q₂ h₁ _ ih₁ ih₂ =>
    intro Q hC hDl hcU hcL
    cases hC
    have hcnt := solve_simple_count exD l c h₁ _ rfl hcU
    have hcL' : c k ∈ Lo' := by
      rw [← List.count_pos_iff] at hcL ⊢; omega
    simp only [SConstr.add_L, Multiset.mem_add, not_or]
    exact ⟨ih₁ _ rfl hDl hcU hcL, ih₂ _ rfl hDl hcU hcL'⟩

/-- ... but the solver of Figure 9, with the atomic solver of Figure 10b, cannot solve it from
the given linear `C`: the inner `useC` has `C` both unrestricted (local) and linear (outer)
in scope, and no rule of Figure 10b applies then (the solver does not guess). -/
theorem ambiguous2_not_solved (l : (k : Nat) → Atom Unit k) :
    ¬ Solve exD (fun k => simpleSolver (l k)) ∅ [] [cAtom] ambiguous2W [] := by
  intro h
  unfold ambiguous2W ambiguousW at h
  cases h with
  | mult h₁ _ =>
    cases h₁ with
    | implOne l₀ hl₀ hin _ =>
      have hl₀' : l₀ = [] := by
        have : (l₀ : Multiset (Atom Unit 0)) = 0 := by rw [hl₀]; rfl
        simpa using this
      subst hl₀'
      have hw : Weakening.wk 0 (cAtom : Atom Unit 0) = cAtom := rfl
      refine solve_simple_stuck l (fun _ => cAtom) hin _ rfl (by simp) ?_ ?_ ?_
      · simp [SConstr.atom]
      · simp [hw]
      · simp [givenC, SConstr.atom]

-- [PAPER ◀ END] §6.3.2, `ambiguous2`

end Examples

end LQT
