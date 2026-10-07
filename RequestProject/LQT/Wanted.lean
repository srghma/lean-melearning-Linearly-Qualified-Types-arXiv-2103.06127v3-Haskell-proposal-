module

public import RequestProject.LQT.Entailment
public import RequestProject.LQT.Map

/-!
# Wanted constraints and their entailment (§6.1, Figure 7)

Paper location: §6.1 "Wanted constraints" (grammar of `C`, scaling of wanted constraints,
Figure 7 "Wanted-constraint entailment", Lemmas 6.1, 6.2, 6.3) and Appendix B.6 (Lemmas B.5
and B.6).  The start and end of each part is marked by `-- [PAPER ▶ START]` /
`-- [PAPER ◀ END]` comments.

**Type variables.**  With type polymorphism, atomic constraints mention type variables (as in
`RW n`).  Type variables are de Bruijn indices: `A k` is the set of atomic constraints with
`k` type variables in scope, and atoms can be *weakened* to a larger scope (`Weakening`).
Accordingly the constraint domain is a family of domains `D k` (`LDomain`), one for each
number of type variables in scope.

Wanted constraints `C ::= Q | C₁ ⊗ C₂ | C₁ & C₂ | π·∀ā.(Q ⊸ C)` are indexed by the number of
type variables in scope.  The paper's implication `π·(Q ⊸ C)` comes with fresh type
variables `ā` (rules G_Unpack and G_LetSig); here they are bound explicitly: `impl π j Q C`
binds `j` type variables in `Q` and `C`.  Rule C_Impl then weakens the assumption:
`Q ⊗ Q₂ ⊢ C` (with `Q` weakened under the `j` new variables) gives `Q ⊢ π·∀ā.(Q₂ ⊸ C)`.

We prove Lemma 6.1 (inversion), Lemma 6.2 (scaling), Lemma 6.3 (inversion of scaling),
Lemma B.5 (weakening of wanteds) and Lemma B.6 (`π·(ρ·C) = (π⋅ρ)·C`).  As for simple
constraints, the impl-case of Lemma 6.1 and Lemma 6.3 only hold "up to `𝒟`" for lawful
domains; the paper's exact statements are recovered for domains satisfying the paper's laws.
-/

@[expose] public section

namespace LQT

open SConstr

-- [NOT IN PAPER ▶ START] type-variable levels: weakening of atoms and families of domains `LDomain`
--   (the paper has no explicit scopes for type variables)
/-- A family of sets of atomic constraints, indexed by the number of type variables in scope,
with weakening of atoms to a larger scope (the new variables are added at the end). -/
class Weakening (A : Nat → Type) where
  /-- Weakening of an atom by `j` new type variables. -/
  wk : {k : Nat} → (j : Nat) → A k → A (k + j)

variable {A : Nat → Type} [∀ k, DecidableEq (A k)] [Weakening A]

/-- Weakening of a simple constraint by `j` new type variables. -/
def SConstr.wk {k : Nat} (j : Nat) (Q : SConstr (A k)) : SConstr (A (k + j)) :=
  Q.map (Weakening.wk j)

@[simp] lemma SConstr.wk_zero {k j : Nat} : (0 : SConstr (A k)).wk j = 0 := map_zero _
@[simp] lemma SConstr.wk_add {k j : Nat} (Q₁ Q₂ : SConstr (A k)) :
    (Q₁ + Q₂).wk j = Q₁.wk j + Q₂.wk j := map_add _ _ _
@[simp] lemma SConstr.wk_smul {k j : Nat} (π : Mult) (Q : SConstr (A k)) :
    (π • Q).wk j = π • Q.wk j := map_smul _ _ _

/-- A constraint domain for each number of type variables in scope. -/
abbrev LDomain (A : Nat → Type) := (k : Nat) → Domain (A k)

/-- Lawful families of domains: each domain is lawful, and duplicability and entailment are
stable under weakening (the usual stability of entailment under renaming of type
variables). -/
structure LDomain.Lawful (D : LDomain A) : Prop where
  lawful : ∀ k, (D k).Lawful
  dup_wk : ∀ {k : Nat} (j : Nat) {q : A k}, q ∈ (D k).Dup → Weakening.wk j q ∈ (D (k + j)).Dup
  entails_wk : ∀ {k : Nat} (j : Nat) {Q Q' : SConstr (A k)}, (D k).Entails Q Q' →
    (D (k + j)).Entails (Q.wk j) (Q'.wk j)

-- [NOT IN PAPER ◀ END] type-variable levels

-- [PAPER ▶ START] §6.1 "Wanted constraints": the grammar `C ::= Q | C₁ ⊗ C₂ | C₁ & C₂ | π·(Q ⊸ C)`
--   (here with explicitly bound type variables `π·∀ā.(Q ⊸ C)`)
/-- Wanted constraints `C` with `k` type variables in scope. -/
inductive Wanted (A : Nat → Type) : Nat → Type
  /-- A simple constraint `Q`. -/
  | simple {k} : SConstr (A k) → Wanted A k
  /-- Multiplicative conjunction `C₁ ⊗ C₂`. -/
  | tensor {k} : Wanted A k → Wanted A k → Wanted A k
  /-- Additive conjunction `C₁ & C₂`. -/
  | amp {k} : Wanted A k → Wanted A k → Wanted A k
  /-- Implication `π·∀ā.(Q ⊸ C)`, binding `j` type variables `ā`. -/
  | impl {k} : Mult → (j : Nat) → SConstr (A (k + j)) → Wanted A (k + j) → Wanted A k

namespace Wanted

-- [PAPER ◀ END] §6.1, grammar of wanted constraints

-- [PAPER ▶ START] §6.1: "We can define scaling over wanted constraints by recursion as follows"
--   (definition and its defining equations)
/-- Scaling of wanted constraints. -/
def smul : {k : Nat} → Mult → Wanted A k → Wanted A k
  | _, π, simple Q => simple (π • Q)
  | _, π, tensor C₁ C₂ => tensor (smul π C₁) (smul π C₂)
  | _, .one, amp C₁ C₂ => amp C₁ C₂
  | _, .omega, amp C₁ C₂ => tensor (smul .omega C₁) (smul .omega C₂)
  | _, π, impl ρ j Q C => impl (π * ρ) j Q C

instance {k : Nat} : SMul Mult (Wanted A k) := ⟨smul⟩

variable {k : Nat}

omit [Weakening A] in
lemma smul_def (π : Mult) (C : Wanted A k) : π • C = smul π C := rfl

omit [Weakening A] in
@[simp] lemma smul_simple (π : Mult) (Q : SConstr (A k)) : π • simple Q = simple (π • Q) := rfl
omit [Weakening A] in
@[simp] lemma smul_tensor (π : Mult) (C₁ C₂ : Wanted A k) :
    π • tensor C₁ C₂ = tensor (π • C₁) (π • C₂) := rfl
omit [Weakening A] in
@[simp] lemma one_smul_amp (C₁ C₂ : Wanted A k) : (Mult.one : Mult) • amp C₁ C₂ = amp C₁ C₂ :=
  rfl
omit [Weakening A] in
@[simp] lemma omega_smul_amp (C₁ C₂ : Wanted A k) :
    (Mult.omega : Mult) • amp C₁ C₂ = tensor ((Mult.omega : Mult) • C₁) ((Mult.omega : Mult) • C₂) :=
  rfl
omit [Weakening A] in
@[simp] lemma smul_impl (π ρ : Mult) (j : Nat) (Q : SConstr (A (k + j))) (C : Wanted A (k + j)) :
    π • impl ρ j Q C = impl (π * ρ) j Q C := rfl

-- [PAPER ◀ END] §6.1, scaling of wanted constraints

-- [NOT IN PAPER ▶ START] `1·C = C`
omit [Weakening A] in
@[simp] lemma one_smul (C : Wanted A k) : (Mult.one : Mult) • C = C := by
  induction C with
  | simple Q => rfl
  | tensor C₁ C₂ ih₁ ih₂ => simp [ih₁, ih₂]
  | amp C₁ C₂ _ _ => rfl
  | impl ρ j Q C _ => simp

-- [NOT IN PAPER ◀ END] `1·C = C`

-- [PAPER ▶ START] Appendix B.6 › Lemma B.6: `π·(ρ·C) = (π⋅ρ)·C`
omit [Weakening A] in
/-- **Lemma B.6.** `π · (ρ · C) = (π ⋅ ρ) · C`. -/
theorem smul_smul (π ρ : Mult) (C : Wanted A k) : π • (ρ • C) = (π * ρ) • C := by
  induction C with
  | simple Q => simp [_root_.smul_smul]
  | tensor C₁ C₂ ih₁ ih₂ => simp [ih₁, ih₂]
  | amp C₁ C₂ ih₁ ih₂ =>
    cases π <;> cases ρ <;> simp_all
  | impl σ j Q C _ => simp [mul_assoc]

-- [PAPER ◀ END] Appendix B.6 › Lemma B.6

end Wanted

namespace LDomain

-- [PAPER ▶ START] §6.1 › Figure 7 "Wanted-constraint entailment": rules C_Dom, C_Id, C_Tensor,
--   C_With, C_Impl
/-- Wanted-constraint entailment `Q ⊢ C` (Figure 7). -/
inductive WEntails (D : LDomain A) : {k : Nat} → SConstr (A k) → Wanted A k → Prop
  /-- C_Dom -/
  | dom {k} {Q₁ Q₂ : SConstr (A k)} {C} : (D k).Entails Q₁ Q₂ → WEntails D Q₂ C →
      WEntails D Q₁ C
  /-- C_Id -/
  | id {k} (Q : SConstr (A k)) : WEntails D Q (.simple Q)
  /-- C_Tensor -/
  | tensor {k} {Q₁ Q₂ : SConstr (A k)} {C₁ C₂} : WEntails D Q₁ C₁ → WEntails D Q₂ C₂ →
      WEntails D (Q₁ + Q₂) (.tensor C₁ C₂)
  /-- C_With -/
  | amp {k} {Q : SConstr (A k)} {C₁ C₂} : WEntails D Q C₁ → WEntails D Q C₂ →
      WEntails D Q (.amp C₁ C₂)
  /-- C_Impl (the assumption `Q₀` is weakened under the bound type variables) -/
  | impl {k j} {Q₀ : SConstr (A k)} {Q₁ : SConstr (A (k + j))} {C} (π : Mult) :
      WEntails D (Q₀.wk j + Q₁) C → WEntails D (π • Q₀) (.impl π j Q₁ C)

-- [PAPER ◀ END] §6.1 › Figure 7

namespace Lawful

variable {D : LDomain A} (hD : D.Lawful)
include hD

-- [NOT IN PAPER ▶ START] helper: `Q ⊢ Q'` iff `Q ⊩ Q'`
/-- On simple wanted constraints, `Q ⊢ Q'` coincides with `Q ⊩ Q'`. -/
theorem wentails_simple_iff {k : Nat} {Q Q' : SConstr (A k)} :
    D.WEntails Q (.simple Q') ↔ (D k).Entails Q Q' := by
  constructor
  · intro h
    generalize hC : Wanted.simple Q' = C at h
    induction h with
    | dom h₁ _ ih => exact (hD.lawful _).trans h₁ (ih hC)
    | id Q => cases hC; exact (hD.lawful _).refl _
    | tensor => cases hC
    | amp => cases hC
    | impl => cases hC
  · intro h
    exact .dom h (.id _)

-- [NOT IN PAPER ◀ END] helper

-- [PAPER ▶ START] Appendix B.6 › Lemma B.5 "Weakening of wanteds"
/-- **Lemma B.5 (Weakening of wanteds).** -/
theorem wentails_weaken {k : Nat} {Q₀ : SConstr (A k)} {C₀ : Wanted A k}
    (Q' : SConstr (A k)) (h : D.WEntails Q₀ C₀) :
    D.WEntails ((Mult.omega : Mult) • Q' + Q₀) C₀ :=
  .dom ((hD.lawful k).weaken Q' ((hD.lawful k).refl _)) h

-- [PAPER ◀ END] Appendix B.6 › Lemma B.5

-- [NOT IN PAPER ▶ START] helpers: discarding duplicable assumptions; weakening preserves
--   duplicability
/-- Discarding duplicable assumptions in wanted entailment. -/
theorem wentails_weaken_dup {k : Nat} {Q QD : SConstr (A k)} {C : Wanted A k}
    (hQD : QD.InDup (D k).Dup) (h : D.WEntails Q C) : D.WEntails (Q + QD) C :=
  .dom ((hD.lawful k).weaken_dup hQD ((hD.lawful k).refl _)) h

/-- Weakened duplicable constraints are duplicable. -/
lemma inDup_wk {k : Nat} (j : Nat) {QD : SConstr (A k)} (h : QD.InDup (D k).Dup) :
    (QD.wk j).InDup (D (k + j)).Dup :=
  map_inDup _ (fun _ hq => hD.dup_wk j hq) h

-- [NOT IN PAPER ◀ END] helpers

-- [PAPER ▶ START] §6.1 › Lemma 6.1 "Inversion" (three cases: tensor, with, implication; proof:
--   Appendix B.6)
/-- **Lemma 6.1 (Inversion), tensor case.** -/
theorem inv_tensor {k : Nat} {Q : SConstr (A k)} {C₁ C₂ : Wanted A k}
    (h : D.WEntails Q (.tensor C₁ C₂)) :
    ∃ Q₁ QD Q₂, QD.InDup (D k).Dup ∧ Q = Q₁ + QD + Q₂ ∧ D.WEntails (Q₁ + QD) C₁ ∧
      D.WEntails (QD + Q₂) C₂ := by
  generalize hC : Wanted.tensor C₁ C₂ = C at h
  induction h with
  | @dom k Q Q' C h₁ _ ih =>
    have hk := hD.lawful k
    obtain ⟨A₁, E, B, hE, rfl, hA, hB⟩ := ih hC
    have h2 : (D k).Entails (A₁ + E + B) ((A₁ + E) + (E + B)) :=
      hk.combine hE (hk.refl (A₁ + E)) (hk.refl (E + B))
    obtain ⟨X, F, Y, hF, rfl, hX, hY⟩ := hk.tensor_inv (hk.trans h₁ h2)
    exact ⟨X, F, Y, hF, rfl, .dom hX hA, .dom hY hB⟩
  | id => cases hC
  | @tensor k Q₁ Q₂ C₁' C₂' h₁ h₂ =>
    cases hC
    exact ⟨Q₁, 0, Q₂, inDup_zero _, by simp, by simpa using h₁, by simpa using h₂⟩
  | amp => cases hC
  | impl => cases hC

omit hD in
/-- **Lemma 6.1 (Inversion), with case.** -/
theorem inv_amp {k : Nat} {Q : SConstr (A k)} {C₁ C₂ : Wanted A k}
    (h : D.WEntails Q (.amp C₁ C₂)) : D.WEntails Q C₁ ∧ D.WEntails Q C₂ := by
  generalize hC : Wanted.amp C₁ C₂ = C at h
  induction h with
  | dom h₁ _ ih => exact ⟨.dom h₁ (ih hC).1, .dom h₁ (ih hC).2⟩
  | id => cases hC
  | tensor => cases hC
  | amp h₁ h₂ => cases hC; exact ⟨h₁, h₂⟩
  | impl => cases hC

/-- **Lemma 6.1 (Inversion), implication case**, repaired "up to `𝒟`": if
`Q ⊢ π·∀ā.(Q₂ ⊸ C)` then `Q = π·Q₁ ⊗ Q_𝒟` with `Q_𝒟 ∈ 𝒟` and `Q₁ ⊗ Q₂ ⊢ C` (with `Q₁`
weakened under `ā`). -/
theorem inv_impl {k j : Nat} {Q : SConstr (A k)} {Q₂ : SConstr (A (k + j))} {π : Mult}
    {C : Wanted A (k + j)} (h : D.WEntails Q (.impl π j Q₂ C)) :
    ∃ Q₁ QD, QD.InDup (D k).Dup ∧ Q = π • Q₁ + QD ∧ D.WEntails (Q₁.wk j + Q₂) C := by
  generalize hC : Wanted.impl π j Q₂ C = C' at h
  induction h with
  | @dom k Q Q' _ h₁ _ ih =>
    obtain ⟨Q₁, QD, hQD, rfl, hW⟩ := ih hC
    have hk := hD.lawful k
    have hkj := hD.lawful (k + j)
    cases π with
    | one =>
      refine ⟨Q, 0, inDup_zero _, by simp, .dom ?_ hW⟩
      have h₁' := hD.entails_wk j h₁
      simp only [one_smul', SConstr.wk_add] at h₁'
      have : (D (k + j)).Entails (Q.wk j + Q₂) (Q₁.wk j + QD.wk j + Q₂) :=
        hkj.tensor h₁' (hkj.refl _)
      refine hkj.trans this ?_
      have e : Q₁.wk j + QD.wk j + Q₂ = (Q₁.wk j + Q₂) + QD.wk j := by abel
      rw [e]; exact hkj.weaken_dup (hD.inDup_wk j hQD) (hkj.refl _)
    | omega =>
      have hQ : Q.InDup (D k).Dup :=
        hk.dup_closed (inDup_add_iff.mpr ⟨inDup_omega_smul _ _, hQD⟩) h₁
      have h₂ : (D k).Entails Q ((Mult.omega : Mult) • Q₁) :=
        hk.trans h₁ (hk.weaken_dup hQD (hk.refl _))
      have h₃ := hD.entails_wk j (hk.omega_inv h₂).2
      refine ⟨Q.unr, Q.lin, hQ, ?_, .dom (hkj.tensor h₃ (hkj.refl _)) hW⟩
      rw [omega_smul_unr]; exact unr_add_lin Q
  | id => cases hC
  | tensor => cases hC
  | amp => cases hC
  | @impl k j' Q₀ Q₁ C₀ π₀ h₀ _ =>
    cases hC
    exact ⟨Q₀, 0, inDup_zero _, by simp, h₀⟩

-- [PAPER ◀ END] §6.1 › Lemma 6.1

-- [PAPER ▶ START] §6.1 › Lemma 6.2 "Scaling" (proof: Appendix B.6)
/-- **Lemma 6.2 (Scaling).** If `Q ⊢ C` then `π · Q ⊢ π · C`. -/
theorem wentails_scaling {k : Nat} {Q : SConstr (A k)} {C : Wanted A k} (π : Mult)
    (h : D.WEntails Q C) : D.WEntails (π • Q) (π • C) := by
  induction h with
  | dom h₁ _ ih => exact .dom ((hD.lawful _).scaling π h₁) ih
  | id Q => exact .id _
  | tensor _ _ ih₁ ih₂ => rw [smul_add]; exact .tensor ih₁ ih₂
  | @amp k Q C₁ C₂ h₁ h₂ ih₁ ih₂ =>
    cases π with
    | one => exact .amp h₁ h₂
    | omega =>
      rw [Wanted.omega_smul_amp, ← omega_smul_add_self Q]
      exact .tensor ih₁ ih₂
  | @impl k j Q₀ Q₁ C ρ _ _ =>
    rw [Wanted.smul_impl, _root_.smul_smul]
    exact .impl _ (by assumption)

-- [PAPER ◀ END] §6.1 › Lemma 6.2

-- [NOT IN PAPER ▶ START] auxiliary lemmas for Lemma 6.3
/-- If the unrestricted atoms of `ω · Q'` are among those of `Q` and `Q' ⊢ C`, then
`Q.unr ⊢ C`. -/
lemma unr_wentails_of_omega_subset {k : Nat} {Q Q' : SConstr (A k)} {C : Wanted A k}
    (hU : ((Mult.omega : Mult) • Q').U ⊆ Q.U) (h : D.WEntails Q' C) : D.WEntails Q.unr C :=
  .dom ((hD.lawful k).unr_entails_of_omega_subset hU) h

omit [Weakening A] hD in
/-- The common step of the tensor and with cases of Lemma 6.3. -/
lemma scaling_inv_aux {k : Nat} {A₁ E B A' B' QD₁ QD₂ : SConstr (A k)}
    (hAE : A₁ + E = (Mult.omega : Mult) • A' + QD₁) (hEB : E + B = (Mult.omega : Mult) • B' + QD₂)
    (hQD₁ : QD₁.InDup (D k).Dup) (hQD₂ : QD₂.InDup (D k).Dup) :
    (A₁ + E + B).InDup (D k).Dup ∧ ((Mult.omega : Mult) • A').U ⊆ (A₁ + E + B).U ∧
      ((Mult.omega : Mult) • B').U ⊆ (A₁ + E + B).U := by
  refine ⟨?_, ?_, ?_⟩
  · have h1 : (A₁ + E).InDup (D k).Dup := by
      rw [hAE]; exact inDup_add_iff.mpr ⟨inDup_omega_smul _ _, hQD₁⟩
    have h2 : (E + B).InDup (D k).Dup := by
      rw [hEB]; exact inDup_add_iff.mpr ⟨inDup_omega_smul _ _, hQD₂⟩
    exact inDup_add_iff.mpr ⟨h1, (inDup_add_iff.mp h2).2⟩
  · have : ((Mult.omega : Mult) • A').U ⊆ (A₁ + E).U := by
      rw [hAE]; exact Finset.subset_union_left
    exact this.trans Finset.subset_union_left
  · have : ((Mult.omega : Mult) • B').U ⊆ (E + B).U := by
      rw [hEB]; exact Finset.subset_union_left
    refine this.trans ?_
    intro x; simp; tauto

-- [NOT IN PAPER ◀ END] auxiliary lemmas for Lemma 6.3

-- [PAPER ▶ START] §6.1 › Lemma 6.3 "Inversion of scaling" (repaired form; proof: Appendix B.6)
/-- **Lemma 6.3 (Inversion of scaling)**, repaired "up to `𝒟`": if `Q ⊢ π · C` then
`Q = π · Q' ⊗ Q_𝒟` with `Q_𝒟 ∈ 𝒟` and `Q' ⊢ C`. -/
theorem wentails_scaling_inv {k : Nat} {Q : SConstr (A k)} {C : Wanted A k} (π : Mult)
    (h : D.WEntails Q (π • C)) :
    ∃ Q' QD, QD.InDup (D k).Dup ∧ Q = π • Q' + QD ∧ D.WEntails Q' C := by
  cases π with
  | one => exact ⟨Q, 0, inDup_zero _, by simp, by simpa using h⟩
  | omega =>
    induction C with
    | simple Q₂ =>
      obtain ⟨Q', QD, hQD, rfl, h'⟩ :=
        (hD.lawful _).scaling_inv .omega ((hD.wentails_simple_iff).mp h)
      exact ⟨Q', QD, hQD, rfl, (hD.wentails_simple_iff).mpr h'⟩
    | tensor C₁ C₂ ih₁ ih₂ =>
      obtain ⟨A₁, E, B, hE, rfl, hA, hB⟩ := hD.inv_tensor h
      obtain ⟨A', QD₁, hQD₁, hAE, hA'⟩ := ih₁ hA
      obtain ⟨B', QD₂, hQD₂, hEB, hB'⟩ := ih₂ hB
      obtain ⟨hin, hsA, hsB⟩ := scaling_inv_aux (D := D) hAE hEB hQD₁ hQD₂
      refine ⟨(A₁ + E + B).unr, (A₁ + E + B).lin, hin, ?_, ?_⟩
      · rw [omega_smul_unr]; exact unr_add_lin _
      · rw [← add_self_of_unrestricted (unrestricted_unr (A₁ + E + B))]
        exact .tensor (hD.unr_wentails_of_omega_subset hsA hA')
          (hD.unr_wentails_of_omega_subset hsB hB')
    | amp C₁ C₂ ih₁ ih₂ =>
      rw [Wanted.omega_smul_amp] at h
      obtain ⟨A₁, E, B, hE, rfl, hA, hB⟩ := hD.inv_tensor h
      obtain ⟨A', QD₁, hQD₁, hAE, hA'⟩ := ih₁ hA
      obtain ⟨B', QD₂, hQD₂, hEB, hB'⟩ := ih₂ hB
      obtain ⟨hin, hsA, hsB⟩ := scaling_inv_aux (D := D) hAE hEB hQD₁ hQD₂
      refine ⟨(A₁ + E + B).unr, (A₁ + E + B).lin, hin, ?_, ?_⟩
      · rw [omega_smul_unr]; exact unr_add_lin _
      · exact .amp (hD.unr_wentails_of_omega_subset hsA hA')
          (hD.unr_wentails_of_omega_subset hsB hB')
    | impl ρ j Q₁ C _ =>
      rw [Wanted.smul_impl] at h
      obtain ⟨Q₀, QD, hQD, rfl, h'⟩ := hD.inv_impl h
      refine ⟨ρ • Q₀, QD, hQD, ?_, .impl ρ h'⟩
      rw [_root_.smul_smul]

-- [PAPER ◀ END] §6.1 › Lemma 6.3

end Lawful

/-! ### The paper's exact statements, for domains satisfying the paper's laws -/

section PaperLaws

variable {D : LDomain A} (hP : ∀ k, (D k).PaperLaws) (hD : D.Lawful)
include hP hD

-- [PAPER ▶ START] §6.1 › Lemma 6.1 "Inversion", implication case, exactly as stated in the paper
/-- **Lemma 6.1 (Inversion), implication case**, as stated in the paper (valid for domains
satisfying the paper's laws). -/
theorem PaperLaws.inv_impl {k j : Nat} {Q : SConstr (A k)} {Q₂ : SConstr (A (k + j))}
    {π : Mult} {C : Wanted A (k + j)} (h : D.WEntails Q (.impl π j Q₂ C)) :
    ∃ Q₁, Q = π • Q₁ ∧ D.WEntails (Q₁.wk j + Q₂) C := by
  obtain ⟨Q₁, QD, hQD, rfl, h'⟩ := hD.inv_impl h
  have hU := ((hP k).inDup_iff_unrestricted).mp hQD
  refine ⟨Q₁ + QD, ?_, ?_⟩
  · cases π with
    | one => rfl
    | omega => rw [smul_add, omega_smul_of_unrestricted hU]
  · have e : (Q₁ + QD).wk j + Q₂ = (Q₁.wk j + Q₂) + QD.wk j := by simp; abel
    rw [e]; exact hD.wentails_weaken_dup (hD.inDup_wk j hQD) h'

-- [PAPER ◀ END] §6.1 › Lemma 6.1 (paper form)

-- [PAPER ▶ START] §6.1 › Lemma 6.3 "Inversion of scaling", exactly as stated in the paper
/-- **Lemma 6.3 (Inversion of scaling)**, as stated in the paper (valid for domains satisfying
the paper's laws). -/
theorem PaperLaws.wentails_scaling_inv {k : Nat} {Q : SConstr (A k)} {C : Wanted A k}
    (π : Mult) (h : D.WEntails Q (π • C)) : ∃ Q', Q = π • Q' ∧ D.WEntails Q' C := by
  obtain ⟨Q', QD, hQD, rfl, h'⟩ := hD.wentails_scaling_inv π h
  have hU := ((hP k).inDup_iff_unrestricted).mp hQD
  refine ⟨Q' + QD, ?_, hD.wentails_weaken_dup hQD h'⟩
  cases π with
  | one => rfl
  | omega => rw [smul_add, omega_smul_of_unrestricted hU]

-- [PAPER ◀ END] §6.1 › Lemma 6.3 (paper form)

end PaperLaws

end LDomain

end LQT
