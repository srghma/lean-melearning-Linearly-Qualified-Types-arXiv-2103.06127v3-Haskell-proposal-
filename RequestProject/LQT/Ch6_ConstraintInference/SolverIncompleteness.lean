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

end Examples

end LQT
