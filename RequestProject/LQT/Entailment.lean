module

public import RequestProject.LQT.Basic

/-!
# The entailment relation on simple constraints (§5.1, Figure 4)

Paper location: §5.1 "Simple Constraints and Entailment" (Definition 5.3, Figure 4,
Lemmas 5.4 and 5.5, Corollary 5.6) and Appendix B (Lemmas B.2, B.3, B.4).  The start and end
of each part is marked by `-- [PAPER ▶ START]` / `-- [PAPER ◀ END]` comments.

The qualified type system is parameterised by an entailment relation `Q₁ ⊩ Q₂` between simple
constraints and a set `𝒟` of duplicable atomic constraints (Definition 5.3).  We bundle these
two parameters in a `Domain`.

The paper requires the relation to obey the twelve laws of Figure 4.  We record them as
`Domain.PaperLaws`.  **These laws are contradictory as soon as `𝒟` is non-empty**
(`Domain.PaperLaws.dup_eq_empty`): if `q ∈ 𝒟` then `ω·q ⊗ 1·q ⊩ ω·q` by laws (1), (5), (11),
and law (7) would force `ω·q ⊗ 1·q` to be of the form `ω·Q'`, which has no linear part.

Since the paper uses `𝒟` precisely to model the `Linearly` constraint, we also introduce the
repaired set of laws `Domain.Lawful`, in which law (7) is weakened "up to `𝒟`", in the same way
as the paper's own Lemma 6.1 is stated "up to the set `𝒟`":

  (7') if `Q ⊩ (π·ρ)·q` then `Q = π·Q' ⊗ Q_𝒟` with `Q_𝒟 ∈ 𝒟` and `Q' ⊩ ρ·q`.

Every domain satisfying the paper's laws satisfies the repaired laws
(`Domain.PaperLaws.toLawful`), and the repaired laws are satisfiable with a non-empty `𝒟`
(see `RequestProject/LQT/FreeDomain.lean`).  All the results of the paper are proved below
for lawful domains.
-/

@[expose] public section

namespace LQT

open SConstr

-- [PAPER ▶ START] §5.1 › Definition 5.3 "Entailment relation": the relation `Q₁ ⊩ Q₂` and the set
--   `𝒟` of duplicable atomic constraints
/-- A constraint domain: an entailment relation `Q₁ ⊩ Q₂` on simple constraints together with
the set `𝒟` (`Dup`) of duplicable atomic constraints (Definition 5.3). -/
structure Domain (A : Type*) where
  /-- The entailment relation `Q₁ ⊩ Q₂`. -/
  Entails : SConstr A → SConstr A → Prop
  /-- The set `𝒟` of duplicable (and discardable) atomic constraints. -/
  Dup : Set A

namespace Domain

variable {A : Type*} [DecidableEq A]

-- [PAPER ◀ END] §5.1 › Definition 5.3

-- [PAPER ▶ START] §5.1 › Figure 4 "Requirements for the entailment relation `Q₁ ⊩ Q₂`" (laws
--   (1)–(12); law (7) is in `PaperLaws`, its repaired version (7') in `Lawful`)
/-- The laws of Figure 4 that are kept unchanged in the repaired version (all except (7)). -/
structure CommonLaws (D : Domain A) : Prop where
  /-- (1) -/
  refl : ∀ Q, D.Entails Q Q
  /-- (2) -/
  cut : ∀ {Q Q₁ Q₂ Q₃}, D.Entails Q₁ Q₂ → D.Entails (Q + Q₂) Q₃ → D.Entails (Q + Q₁) Q₃
  /-- (3) -/
  tensor_inv : ∀ {Q Q₁ Q₂}, D.Entails Q (Q₁ + Q₂) →
    ∃ Q' QD Q'', QD.InDup D.Dup ∧ Q = Q' + QD + Q'' ∧ D.Entails (Q' + QD) Q₁ ∧
      D.Entails (QD + Q'') Q₂
  /-- (4) -/
  empty_inv : ∀ {Q}, D.Entails Q 0 → Q.InDup D.Dup
  /-- (5) -/
  tensor : ∀ {Q₁ Q₁' Q₂ Q₂'}, D.Entails Q₁ Q₁' → D.Entails Q₂ Q₂' →
    D.Entails (Q₁ + Q₂) (Q₁' + Q₂')
  /-- (6) -/
  scale_atom : ∀ {Q ρ q} (π : Mult), D.Entails Q (atom ρ q) → D.Entails (π • Q) (atom (π * ρ) q)
  /-- (8) -/
  derelict : ∀ {Q₁ Q₂}, D.Entails Q₁ Q₂ → D.Entails ((Mult.omega : Mult) • Q₁) Q₂
  /-- (9) -/
  weaken : ∀ {Q₁ Q₂} (Q' : SConstr A), D.Entails Q₁ Q₂ →
    D.Entails ((Mult.omega : Mult) • Q' + Q₁) Q₂
  /-- (10) -/
  dup : ∀ {q}, q ∈ D.Dup → D.Entails (atom .one q) (atom .one q + atom .one q)
  /-- (11) -/
  discard : ∀ {q}, q ∈ D.Dup → D.Entails (atom .one q) 0
  /-- (12) -/
  dup_closed : ∀ {Q Q'}, Q.InDup D.Dup → D.Entails Q' Q → Q'.InDup D.Dup

/-- The requirements of Figure 4 of the paper, verbatim. -/
structure PaperLaws (D : Domain A) : Prop extends CommonLaws D where
  /-- (7) -/
  scale_atom_inv : ∀ {Q π ρ q}, D.Entails Q (atom (π * ρ) q) →
    ∃ Q', Q = π • Q' ∧ D.Entails Q' (atom ρ q)

/-- The repaired requirements: Figure 4 with law (7) weakened "up to `𝒟`". -/
structure Lawful (D : Domain A) : Prop extends CommonLaws D where
  /-- (7') -/
  scale_atom_inv : ∀ {Q π ρ q}, D.Entails Q (atom (π * ρ) q) →
    ∃ Q' QD, QD.InDup D.Dup ∧ Q = π • Q' + QD ∧ D.Entails Q' (atom ρ q)

-- [PAPER ◀ END] §5.1 › Figure 4

-- [NOT IN PAPER ▶ START] consistency analysis of the laws of Figure 4 (finding of the
--   formalization: the laws, as stated, force `𝒟 = ∅`)
/-- The laws of Figure 4 force the set `𝒟` of duplicable constraints to be empty. -/
theorem PaperLaws.dup_eq_empty {D : Domain A} (h : D.PaperLaws) : D.Dup = ∅ := by
  ext q
  simp only [Set.mem_empty_iff_false, iff_false]
  intro hq
  have h1 : D.Entails (atom .omega q + atom .one q) (atom .omega q + 0) :=
    h.tensor (h.refl _) (h.discard hq)
  rw [add_zero] at h1
  have h2 : D.Entails (atom .omega q + atom .one q) (atom (Mult.omega * Mult.omega) q) := h1
  obtain ⟨Q', hQ', -⟩ := h.scale_atom_inv h2
  have := congrArg SConstr.L hQ'
  simp at this

/-- The paper's laws imply the repaired laws. -/
theorem PaperLaws.toLawful {D : Domain A} (h : D.PaperLaws) : D.Lawful where
  toCommonLaws := h.toCommonLaws
  scale_atom_inv hQ := by
    obtain ⟨Q', h1, h2⟩ := h.scale_atom_inv hQ
    exact ⟨Q', 0, inDup_zero _, by rw [add_zero]; exact h1, h2⟩

-- [NOT IN PAPER ◀ END] consistency analysis of Figure 4

/-! ## Consequences of the (repaired) laws -/

namespace Lawful

variable {D : Domain A} (hD : D.Lawful)
include hD

-- [NOT IN PAPER ▶ START] elementary consequences of the laws, used by the proofs
lemma trans {Q₁ Q₂ Q₃ : SConstr A} (h₁ : D.Entails Q₁ Q₂) (h₂ : D.Entails Q₂ Q₃) :
    D.Entails Q₁ Q₃ := by
  have := hD.cut (Q := 0) h₁ (by rwa [zero_add])
  rwa [zero_add] at this

lemma entails_of_eq {Q₁ Q₂ : SConstr A} (h : Q₁ = Q₂) : D.Entails Q₁ Q₂ := h ▸ hD.refl _

/-- Weakening by an arbitrary unrestricted constraint. -/
lemma weaken_unr {W Q₁ Q₂ : SConstr A} (hW : W.Unrestricted) (h : D.Entails Q₁ Q₂) :
    D.Entails (W + Q₁) Q₂ := by
  have := hD.weaken W h
  rwa [omega_smul_of_unrestricted hW] at this

lemma unr_entails_zero (Q : SConstr A) : D.Entails Q.unr 0 := by
  have := hD.weaken_unr (unrestricted_unr Q) (hD.refl 0)
  rwa [add_zero] at this

/-- `ω · Q ⊩ Q`. -/
lemma omega_smul_entails (Q : SConstr A) : D.Entails ((Mult.omega : Mult) • Q) Q :=
  hD.derelict (hD.refl Q)

-- [NOT IN PAPER ◀ END] elementary consequences

-- [PAPER ▶ START] Appendix B.6 › Lemma B.2 "`𝒟` discarding"
/-- Discarding (Lemma B.2, first form): if `Q_𝒟 ∈ 𝒟` then `Q_𝒟 ⊩ ε`. -/
lemma discard_dup {QD : SConstr A} (h : QD.InDup D.Dup) : D.Entails QD 0 := by
  induction QD using SConstr.induction_on' with
  | h0 => exact hD.refl 0
  | hω q Q ih =>
    have h' := (inDup_add_iff.mp h).2
    have := hD.weaken_unr (W := atom .omega q) rfl (ih h')
    exact this
  | h1 q Q ih =>
    obtain ⟨hq, h'⟩ := inDup_add_iff.mp h
    have := hD.tensor (hD.discard (inDup_atom_one_iff.mp hq)) (ih h')
    rwa [add_zero] at this

/-- Discarding (Lemma B.2, second form): if `Q₁ ⊩ Q₂` and `Q_𝒟 ∈ 𝒟` then
`Q₁ ⊗ Q_𝒟 ⊩ Q₂`. -/
lemma weaken_dup {QD Q₁ Q₂ : SConstr A} (h : QD.InDup D.Dup) (h₁ : D.Entails Q₁ Q₂) :
    D.Entails (Q₁ + QD) Q₂ := by
  have := hD.tensor h₁ (hD.discard_dup h)
  rwa [add_zero] at this

-- [PAPER ◀ END] Appendix B.6 › Lemma B.2

-- [PAPER ▶ START] Appendix B.6 › Lemma B.3 "`𝒟` duplication"
/-- Duplication (Lemma B.3, first form): if `Q_𝒟 ∈ 𝒟` then `Q_𝒟 ⊩ Q_𝒟 ⊗ Q_𝒟`. -/
lemma dup_dup {QD : SConstr A} (h : QD.InDup D.Dup) : D.Entails QD (QD + QD) := by
  induction QD using SConstr.induction_on' with
  | h0 => rw [add_zero]; exact hD.refl 0
  | hω q Q ih =>
    have h' := (inDup_add_iff.mp h).2
    have e : atom .omega q + Q + (atom .omega q + Q) =
        (atom .omega q + atom .omega q) + (Q + Q) := by abel
    rw [e, add_self_of_unrestricted (Q := atom .omega q) rfl]
    exact hD.tensor (hD.refl _) (ih h')
  | h1 q Q ih =>
    obtain ⟨hq, h'⟩ := inDup_add_iff.mp h
    have e : atom .one q + Q + (atom .one q + Q) =
        (atom .one q + atom .one q) + (Q + Q) := by abel
    rw [e]
    exact hD.tensor (hD.dup (inDup_atom_one_iff.mp hq)) (ih h')

/-- Duplication (Lemma B.3, second form). -/
lemma dup_contraction {Q₁ QD Q₁' Q₂ Q₂' : SConstr A} (hQD : QD.InDup D.Dup)
    (h₁ : D.Entails (Q₁ + QD) Q₂) (h₂ : D.Entails (QD + Q₁') Q₂') :
    D.Entails (Q₁ + QD + Q₁') (Q₂ + Q₂') := by
  have e : Q₁ + (QD + QD) + Q₁' = (Q₁ + QD) + (QD + Q₁') := by abel
  have h3 : D.Entails (Q₁ + QD + Q₁') (Q₁ + (QD + QD) + Q₁') :=
    hD.tensor (hD.tensor (hD.refl _) (hD.dup_dup hQD)) (hD.refl _)
  rw [e] at h3
  exact hD.trans h3 (hD.tensor h₁ h₂)

-- [PAPER ◀ END] Appendix B.6 › Lemma B.3

-- [NOT IN PAPER ▶ START] auxiliary lemmas (the combination step is used implicitly in the proofs of
--   Appendix B)
/-- The key combination step used throughout the paper's proofs: if `Q_𝒟 ∈ 𝒟`,
`Q₁ ⊗ Q_𝒟 ⊩ X` and `Q_𝒟 ⊗ Q₂ ⊩ Y` then `Q₁ ⊗ Q_𝒟 ⊗ Q₂ ⊩ X ⊗ Y`. -/
lemma combine {Q₁ QD Q₂ X Y : SConstr A} (hQD : QD.InDup D.Dup)
    (h₁ : D.Entails (Q₁ + QD) X) (h₂ : D.Entails (QD + Q₂) Y) :
    D.Entails (Q₁ + QD + Q₂) (X + Y) :=
  hD.dup_contraction hQD h₁ h₂

/-- An unrestricted constraint whose atoms are unrestricted atoms of `Q` is entailed by
`Q.unr`. -/
lemma unr_entails_of_subset {Q X : SConstr A} (hX : X.Unrestricted) (hU : X.U ⊆ Q.U) :
    D.Entails Q.unr X := by
  have := hD.weaken_unr (W := Q.unr) (unrestricted_unr Q) (hD.refl X)
  rwa [unr_add_absorb hX hU] at this

/-- If the unrestricted atoms of `ω · Q'` are among those of `Q`, then `Q.unr ⊩ Q'`. -/
lemma unr_entails_of_omega_subset {Q Q' : SConstr A}
    (hU : ((Mult.omega : Mult) • Q').U ⊆ Q.U) : D.Entails Q.unr Q' :=
  hD.trans (hD.unr_entails_of_subset (unrestricted_omega_smul Q') hU) (hD.omega_smul_entails Q')

-- [NOT IN PAPER ◀ END] auxiliary lemmas

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
version is false as soon as `𝒟 ≠ ∅`, see `FreeDomain.lean`, and is recovered for domains
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

end LQT
