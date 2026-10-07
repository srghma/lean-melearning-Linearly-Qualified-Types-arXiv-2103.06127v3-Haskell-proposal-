module

public import RequestProject.LQT.Ch5_QualifiedTypeSystem.LeveledDomains

/-!
# Wanted constraints and their entailment (§6.1, Figure 7)

Paper location: §6.1 "Wanted constraints" (grammar of `C`, scaling of wanted constraints,
Figure 7 "Wanted-constraint entailment") and Appendix B.6 (Lemma B.6).  Lemmas 6.1, 6.2, 6.3
and B.5 are in `WantedLemmas.lean`.  The start and end of each part is marked by `-- [PAPER ▶ START]` /
`-- [PAPER ◀ END]` comments.

**Type variables.**  Type variables are de Bruijn indices; the constraint domain is a family of
domains `D k` (`LDomain`, see `Ch5_QualifiedTypeSystem/LeveledDomains.lean`), one for each
number of type variables in scope.

Wanted constraints `C ::= Q | C₁ ⊗ C₂ | C₁ & C₂ | π·∀ā.(Q ⊸ C)` are indexed by the number of
type variables in scope.  The paper's implication `π·(Q ⊸ C)` comes with fresh type
variables `ā` (rules G_Unpack and G_LetSig); here they are bound explicitly: `impl π j Q C`
binds `j` type variables in `Q` and `C`.  Rule C_Impl then weakens the assumption:
`Q ⊗ Q₂ ⊢ C` (with `Q` weakened under the `j` new variables) gives `Q ⊢ π·∀ā.(Q₂ ⊸ C)`.

We prove Lemma B.6 (`π·(ρ·C) = (π⋅ρ)·C`) here.
-/

@[expose] public section

namespace LQT

open SConstr

variable {A : Nat → Type} [∀ k, DecidableEq (A k)] [Weakening A]

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

end LDomain

end LQT
