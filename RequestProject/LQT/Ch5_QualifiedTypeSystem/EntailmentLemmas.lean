module

public import RequestProject.LQT.Ch5_QualifiedTypeSystem.Entailment

/-!
# Scaling lemmas for entailment (§5.1, Lemmas 5.4, 5.5, Corollary 5.6)

Paper location: §5.1 "Simple Constraints and Entailment" (Lemma 5.4 "Scaling", Lemma 5.5
"Inversion of scaling", Corollary 5.6 "Linear assumptions", and the remark after Figure 4 that
`1·q ⊩ ω·q` is prohibited) and Appendix B.6 (Lemma B.4 "Transitive tensor decomposition").  The
start and end of each part is marked by `-- [PAPER ▶ START]` / `-- [PAPER ◀ END]` comments.

Lemma 5.5 and Corollary 5.6 are proved in a repaired form for lawful domains
(`Domain.Lawful.scaling_inv`, `Domain.Lawful.linear_assumptions`), and exactly as stated in the
paper for domains satisfying the paper's laws (`Domain.PaperLaws.scaling_inv`,
`Domain.PaperLaws.linear_assumptions`).
-/

@[expose] public section

namespace LQT

open SConstr

namespace Domain

variable {A : Type*} [DecidableEq A]

namespace Lawful

variable {D : Domain A} (hD : D.Lawful)
include hD

-- [PAPER ▶ START] §5.1 › Lemma 5.4 "Scaling" (proof: Appendix B.5)
/-- **Lemma 5.4 (Scaling).** If `Q₁ ⊩ Q₂` then `π · Q₁ ⊩ π · Q₂`. -/
theorem scaling {Q₁ Q₂ : SConstr A} (π : Mult) (h : D.Entails Q₁ Q₂) :
    D.Entails (π • Q₁) (π • Q₂) := by
  cases π with
  | one => exact h
  | omega =>
    induction Q₂ using SConstr.induction_on' generalizing Q₁ with
    | h0 =>
      rw [smul_zero]
      have := hD.weaken_unr (unrestricted_omega_smul Q₁) (hD.refl 0)
      rwa [add_zero] at this
    | hω q R ih =>
      obtain ⟨A₁, E, B, -, rfl, hA, hB⟩ := hD.tensor_inv h
      have h1 := hD.scale_atom .omega hA
      have h2 := ih hB
      have e : (Mult.omega : Mult) • (A₁ + E + B) =
          (Mult.omega : Mult) • (A₁ + E) + (Mult.omega : Mult) • (E + B) := by
        ext x <;> simp [Finset.mem_union] ; tauto
      rw [e, smul_add _ (atom _ q) R, smul_atom]
      exact hD.tensor h1 h2
    | h1 q R ih =>
      obtain ⟨A₁, E, B, -, rfl, hA, hB⟩ := hD.tensor_inv h
      have h1 := hD.scale_atom .omega hA
      have h2 := ih hB
      have e : (Mult.omega : Mult) • (A₁ + E + B) =
          (Mult.omega : Mult) • (A₁ + E) + (Mult.omega : Mult) • (E + B) := by
        ext x <;> simp [Finset.mem_union] ; tauto
      rw [e, smul_add _ (atom _ q) R, smul_atom]
      exact hD.tensor h1 h2

-- [PAPER ◀ END] §5.1 › Lemma 5.4

-- [NOT IN PAPER ▶ START] the `ω` case of Lemma 5.5, proved separately
/-- Inversion of `ω`-scaling: if `Q₁ ⊩ ω · Q₂` then all linear assumptions of `Q₁` are
duplicable and the unrestricted part of `Q₁` entails `Q₂`. -/
theorem omega_inv {Q₁ Q₂ : SConstr A} (h : D.Entails Q₁ ((Mult.omega : Mult) • Q₂)) :
    Q₁.InDup D.Dup ∧ D.Entails Q₁.unr Q₂ := by
  induction Q₂ using SConstr.induction_on' generalizing Q₁ with
  | h0 =>
    rw [smul_zero] at h
    exact ⟨hD.empty_inv h, hD.unr_entails_zero Q₁⟩
  | hω q R ih =>
    rw [smul_add, smul_atom] at h
    obtain ⟨A₁, E, B, hE, rfl, hA, hB⟩ := hD.tensor_inv h
    obtain ⟨A', QD, hQD, hAE, hA'⟩ := hD.scale_atom_inv (π := .omega) (ρ := .omega) hA
    obtain ⟨hEB, hR⟩ := ih hB
    refine ⟨?_, ?_⟩
    · have h1 : (A₁ + E).InDup D.Dup := by
        rw [hAE]; exact inDup_add_iff.mpr ⟨inDup_omega_smul _ _, hQD⟩
      have := inDup_add_iff.mp h1
      exact inDup_add_iff.mpr ⟨h1, (inDup_add_iff.mp hEB).2⟩
    · have hsub1 : ((Mult.omega : Mult) • A').U ⊆ (A₁ + E + B).U := by
        have : ((Mult.omega : Mult) • A').U ⊆ (A₁ + E).U := by
          rw [hAE]; exact Finset.subset_union_left
        exact this.trans Finset.subset_union_left
      have k1 : D.Entails (A₁ + E + B).unr (atom .omega q) :=
        hD.trans (hD.unr_entails_of_omega_subset hsub1) hA'
      have hsub2 : ((Mult.omega : Mult) • (E + B).unr).U ⊆ (A₁ + E + B).U := by
        rw [omega_smul_unr]; intro x; simp; tauto
      have k2 : D.Entails (A₁ + E + B).unr R :=
        hD.trans (hD.unr_entails_of_omega_subset hsub2) hR
      have := hD.tensor k1 k2
      rwa [add_self_of_unrestricted (unrestricted_unr _)] at this
  | h1 q R ih =>
    rw [smul_add, smul_atom] at h
    obtain ⟨A₁, E, B, hE, rfl, hA, hB⟩ := hD.tensor_inv h
    obtain ⟨A', QD, hQD, hAE, hA'⟩ := hD.scale_atom_inv (π := .omega) (ρ := .one) hA
    obtain ⟨hEB, hR⟩ := ih hB
    refine ⟨?_, ?_⟩
    · have h1 : (A₁ + E).InDup D.Dup := by
        rw [hAE]; exact inDup_add_iff.mpr ⟨inDup_omega_smul _ _, hQD⟩
      exact inDup_add_iff.mpr ⟨h1, (inDup_add_iff.mp hEB).2⟩
    · have hsub1 : ((Mult.omega : Mult) • A').U ⊆ (A₁ + E + B).U := by
        have : ((Mult.omega : Mult) • A').U ⊆ (A₁ + E).U := by
          rw [hAE]; exact Finset.subset_union_left
        exact this.trans Finset.subset_union_left
      have k1 : D.Entails (A₁ + E + B).unr (atom .one q) :=
        hD.trans (hD.unr_entails_of_omega_subset hsub1) hA'
      have hsub2 : ((Mult.omega : Mult) • (E + B).unr).U ⊆ (A₁ + E + B).U := by
        rw [omega_smul_unr]; intro x; simp; tauto
      have k2 : D.Entails (A₁ + E + B).unr R :=
        hD.trans (hD.unr_entails_of_omega_subset hsub2) hR
      have := hD.tensor k1 k2
      rwa [add_self_of_unrestricted (unrestricted_unr _)] at this

-- [NOT IN PAPER ◀ END] `ω` case of Lemma 5.5

-- [PAPER ▶ START] §5.1 › Lemma 5.5 "Inversion of scaling" (repaired form; proof: Appendix B.5)
/-- **Lemma 5.5 (Inversion of scaling), repaired.** If `Q₁ ⊩ π · Q₂` then
`Q₁ = π · Q' ⊗ Q_𝒟` with `Q_𝒟 ∈ 𝒟` and `Q' ⊩ Q₂`.  (The paper states it without `Q_𝒟`; that
version is false as soon as `𝒟 ≠ ∅`, see
`Ch6_ConstraintInference/FreeDomain.lean`, and is recovered for domains
satisfying the paper's laws in `PaperLaws.scaling_inv`.) -/
theorem scaling_inv {Q₁ Q₂ : SConstr A} (π : Mult) (h : D.Entails Q₁ (π • Q₂)) :
    ∃ Q' QD, QD.InDup D.Dup ∧ Q₁ = π • Q' + QD ∧ D.Entails Q' Q₂ := by
  cases π with
  | one => exact ⟨Q₁, 0, inDup_zero _, by simp, h⟩
  | omega =>
    obtain ⟨h1, h2⟩ := hD.omega_inv h
    refine ⟨Q₁.unr, Q₁.lin, h1, ?_, h2⟩
    rw [omega_smul_unr]; exact unr_add_lin Q₁

-- [PAPER ◀ END] §5.1 › Lemma 5.5

-- [PAPER ▶ START] §5.1 › Corollary 5.6 "Linear assumptions" (repaired form)
/-- **Corollary 5.6 (Linear assumptions), repaired.** If `Q₁ ⊩ ω · Q₂` then every linear
assumption of `Q₁` is duplicable. -/
theorem linear_assumptions {Q₁ Q₂ : SConstr A} (h : D.Entails Q₁ ((Mult.omega : Mult) • Q₂)) :
    Q₁.InDup D.Dup :=
  (hD.omega_inv h).1

-- [PAPER ◀ END] §5.1 › Corollary 5.6

-- [PAPER ▶ START] Appendix B.6 › Lemma B.4 "Transitive tensor decomposition" (corrected form)
/-- **Lemma B.4 (Transitive tensor decomposition), corrected.**  The statement of the paper
only asks for `Q₁' ⊗ Q_𝒟' ⊩ Q₁`, `Q_𝒟' ⊗ Q₂' ⊩ Q₂` and `Q_𝒟' ⊩ Q_𝒟`, which is trivially
satisfiable (take `Q₁' = Q₁`, `Q_𝒟' = Q_𝒟`, `Q₂' = Q₂`); the intended statement (see its proof
in the paper) also decomposes `Q`.  We prove the decomposition version. -/
theorem transitive_tensor_decomposition {Q Q₁ QD Q₂ : SConstr A} (hQD : QD.InDup D.Dup)
    (h : D.Entails Q (Q₁ + QD + Q₂)) :
    ∃ Q₁' QD' Q₂', QD'.InDup D.Dup ∧ Q = Q₁' + QD' + Q₂' ∧
      D.Entails (Q₁' + QD') Q₁ ∧ D.Entails (QD' + Q₂') Q₂ := by
  rw [add_assoc] at h
  obtain ⟨X, F, Y, hF, rfl, h1, h2⟩ := hD.tensor_inv h
  refine ⟨X, F, Y, hF, rfl, h1, ?_⟩
  have := hD.weaken_dup hQD (hD.refl Q₂)
  rw [add_comm] at this
  exact hD.trans h2 this

-- [PAPER ◀ END] Appendix B.6 › Lemma B.4

end Lawful

/-! ## The paper's statements, for domains satisfying the paper's laws -/

namespace PaperLaws

variable {D : Domain A} (hD : D.PaperLaws)
include hD

-- [NOT IN PAPER ▶ START] helper: with the paper's laws, `Q ∈ 𝒟` means "no linear part"
lemma inDup_iff_unrestricted {Q : SConstr A} : Q.InDup D.Dup ↔ Q.Unrestricted := by
  constructor
  · intro h
    unfold Unrestricted
    rw [Multiset.eq_zero_iff_forall_notMem]
    intro q hq
    have := h q hq
    rw [hD.dup_eq_empty] at this
    exact this
  · exact inDup_of_unrestricted

-- [NOT IN PAPER ◀ END] helper

-- [PAPER ▶ START] §5.1 › Lemma 5.5 "Inversion of scaling", exactly as stated in the paper
/-- **Lemma 5.5 (Inversion of scaling)**, as stated in the paper, holds for domains satisfying
the paper's laws (which force `𝒟 = ∅`). -/
theorem scaling_inv {Q₁ Q₂ : SConstr A} (π : Mult) (h : D.Entails Q₁ (π • Q₂)) :
    ∃ Q', Q₁ = π • Q' ∧ D.Entails Q' Q₂ := by
  obtain ⟨Q', QD, hQD, rfl, h'⟩ := hD.toLawful.scaling_inv π h
  have hU := (hD.inDup_iff_unrestricted).mp hQD
  cases π with
  | one => exact ⟨Q' + QD, by simp, hD.toLawful.weaken_dup hQD h'⟩
  | omega =>
    refine ⟨Q' + QD, ?_, hD.toLawful.weaken_dup hQD h'⟩
    rw [smul_add, omega_smul_of_unrestricted hU]

-- [PAPER ◀ END] §5.1 › Lemma 5.5 (paper form)

-- [PAPER ▶ START] §5.1 › Corollary 5.6 "Linear assumptions", exactly as stated in the paper
/-- **Corollary 5.6 (Linear assumptions)**, as stated in the paper. -/
theorem linear_assumptions {Q₁ Q₂ : SConstr A}
    (h : D.Entails Q₁ ((Mult.omega : Mult) • Q₂)) : Q₁.Unrestricted :=
  (hD.inDup_iff_unrestricted).mp (hD.toLawful.linear_assumptions h)

-- [PAPER ◀ END] §5.1 › Corollary 5.6 (paper form)

end PaperLaws

end Domain

section
variable {A : Type*} [DecidableEq A]

-- [PAPER ▶ START] §5.1, remark after Figure 4: "Crucially, it is not the case that `1·q ⊩ ω·q`
--   for `q ∈ 𝒟`; such an entailment is, in fact, prohibited (Lemma 5.5) by the rules of Figure 4."

/-- In every lawful domain, `1·q ⊩ ω·q` can only hold if `q` is provable from no assumption at
all (`ε ⊩ 1·q`); in particular it never holds for a duplicable atom that is not trivially true. -/
theorem Domain.Lawful.one_entails_omega {D : Domain A} (hD : D.Lawful) {q : A}
    (h : D.Entails (SConstr.atom .one q) (SConstr.atom .omega q)) :
    D.Entails 0 (SConstr.atom .one q) := by
  have e : (SConstr.atom .omega q : SConstr A) = (Mult.omega : Mult) • SConstr.atom .one q := by
    ext <;> simp
  rw [e] at h
  have h' := (hD.omega_inv h).2
  have e' : (SConstr.atom .one q : SConstr A).unr = 0 := by ext <;> simp
  rwa [e'] at h'

-- [PAPER ◀ END] §5.1, `1·q ⊮ ω·q` in lawful domains

end

end LQT
