module

public import RequestProject.LQT.Ch3_LinearConstraints.ExampleSetting
public import RequestProject.LQT.Ch6_ConstraintInference.WantedLemmas

/-!
# `C ⊗ C` versus `C & C` (remark of §6.1)

Paper location: §6.1 "Wanted constraints" (the remark that if `C` is assumed linearly, `C ⊗ C`
is not provable while `C & C` is).  The example uses the setting of the §3.1 examples
(`Ch3_LinearConstraints/ExampleSetting.lean`).

* `with_entailed`: with a single linear assumption `C`, `C & C` is provable;
* `tensor_not_entailed`: with a single linear assumption `C`, `C ⊗ C` is not provable.
-/

@[expose] public section

namespace LQT

namespace Examples

-- [PAPER ▶ START] §6.1 "Wanted constraints": "if `C` is assumed linearly (and we have no other
--   assumptions), then `C ⊗ C` is not provable, while `C & C` is."

/-- With a single linear assumption `C`, `C & C` is provable. -/
theorem with_entailed :
    exD.WEntails (givenC : SConstr (Atom Unit 0)) (.amp (.simple givenC) (.simple givenC)) :=
  .amp (.id _) (.id _)

/-- With a single linear assumption `C`, `C ⊗ C` is not provable. -/
theorem tensor_not_entailed :
    ¬ exD.WEntails (givenC : SConstr (Atom Unit 0)) (.tensor (.simple givenC) (.simple givenC)) := by
  intro h
  have hL := predLDomain_lawful (∅ : Set Unit)
  obtain ⟨Q₁, QD, Q₂, hD, hQ, h₁, h₂⟩ := hL.inv_tensor h
  rw [hL.wentails_simple_iff] at h₁ h₂
  have hU : cAtom ∉ (Q₁ + QD + Q₂).U := by rw [← hQ]; simp
  simp only [SConstr.add_U, Finset.mem_union, not_or] at hU
  obtain ⟨-, c₁⟩ := ent_count h₁ (by simp [hU.1.1, hU.1.2])
  obtain ⟨-, c₂⟩ := ent_count h₂ (by simp [hU.1.2, hU.2])
  have c₀ : (Q₁ + QD + Q₂).L.count cAtom = 1 := by rw [← hQ]; simp
  have cD : QD.L.count cAtom = 0 := by
    rw [Multiset.count_eq_zero]
    intro hm
    simpa using hD _ hm
  simp only [SConstr.add_L, Multiset.count_add, givenC_L, Multiset.count_singleton_self]
    at c₀ c₁ c₂
  omega

-- [PAPER ◀ END] §6.1, `C ⊗ C` versus `C & C`

end Examples

end LQT
