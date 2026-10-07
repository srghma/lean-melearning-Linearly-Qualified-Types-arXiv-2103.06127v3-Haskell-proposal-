module

public import RequestProject.LQT.Ch6_ConstraintInference.Generation

/-!
# Inversion lemmas for constraint generation

Paper location: none.  Constraint generation (Figure 8) is syntax-directed; these lemmas invert
its rules for variables, data constructors, applications and `let`.  They are used to show that
the inference algorithm rejects the programs of §3.2 (`Ch3_LinearConstraints/Linearly.lean`).
-/

@[expose] public section

namespace LQT

-- [NOT IN PAPER ▶ START] inversion lemmas for constraint generation (whole file)

section GenInv
variable {P : Type} {sig : DataSig P} {k n : Nat} {Γ : Fin n → Scheme P k} {u : Fin n → Usage}
  {τ : Ty P k} {C : Wanted (Atom P) k}

lemma genLet_inv {π : Mult} {e₁ : Tm sig k n} {e₂ : Tm sig k (n + 1)}
    (h : Gen sig Γ u (.let_ π e₁ e₂) τ C) :
    ∃ (u₁ u₂ : Fin n → Usage) (τ₁ : Ty P k) (C₁ C₂ : Wanted (Atom P) k),
      u = π • u₁ + u₂ ∧ C = .tensor (π • C₁) C₂ ∧ Gen sig Γ u₁ e₁ τ₁ C₁ ∧
      Gen sig (Fin.cons (Scheme.mono τ₁) Γ) (Fin.cons (Usage.ofMult π) u₂) e₂ τ C₂ := by
  cases h with
  | let_ g₁ g₂ => exact ⟨_, _, _, _, _, rfl, rfl, g₁, g₂⟩

lemma genApp_inv {e₁ e₂ : Tm sig k n} (h : Gen sig Γ u (.app e₁ e₂) τ C) :
    ∃ (u₁ u₂ : Fin n → Usage) (π : Mult) (τ₂ : Ty P k) (C₁ C₂ : Wanted (Atom P) k),
      u = u₁ + π • u₂ ∧ C = .tensor C₁ (π • C₂) ∧ Gen sig Γ u₁ e₁ (.arr π τ₂ τ) C₁ ∧
      Gen sig Γ u₂ e₂ τ₂ C₂ := by
  cases h with
  | app g₁ g₂ => exact ⟨_, _, _, _, _, _, rfl, rfl, g₁, g₂⟩

lemma genVar_inv {x : Fin n} (h : Gen sig Γ u (.var x) τ C) :
    ∃ (v : Fin n → Usage) (τs : Fin (Γ x).j → Ty P k), u = single x + (Mult.omega : Mult) • v ∧
      τ = (Γ x).τ.subst (instSub τs) ∧ C = .simple ((Γ x).Q.tsubst (instSub τs)) := by
  cases h with
  | var v τs hx => subst hx; exact ⟨v, τs, rfl, rfl, rfl⟩

lemma genCon_inv {T : Nat} {i : Fin (sig.ncons T)} (h : Gen sig Γ u (.con T i) τ C) :
    ∃ (v : Fin n → Usage) (τs : Fin (sig.params T) → Ty P k), u = (Mult.omega : Mult) • v ∧
      τ = (sig.conTy T i).subst τs ∧ C = .simple 0 := by
  cases h with
  | con v _ _ τs => exact ⟨v, τs, rfl, rfl, rfl⟩

end GenInv

-- [NOT IN PAPER ◀ END] inversion lemmas for constraint generation

end LQT
