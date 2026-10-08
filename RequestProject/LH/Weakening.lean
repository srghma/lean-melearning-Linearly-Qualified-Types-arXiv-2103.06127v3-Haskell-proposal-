module

public import RequestProject.LH.UsageVec

/-!
# Structural properties of `λq→`: weakening and renaming

No counterpart in the paper (they are used for the substitution lemma and type preservation).

* `HasType.weaken_omega` : variables can be added with multiplicity `ω`
  (`Γ ⊢ t : A` implies `Γ + ω Θ ⊢ t : A`); this is the weakening built into rule (var).
* `HasType.rename` : typing is stable under renaming of term variables (the multiplicities of
  variables identified by the renaming add up).
-/

@[expose] public section

namespace LH

variable {S : Sig}

-- [NOT IN PAPER ▶ START] weakening and renaming
theorem omega_smul_wkU {m n : Nat} (θ : Fin n → Usage m) :
    (Usage.omega : Usage (m + 1)) • wkU θ = wkU ((Usage.omega : Usage m) • θ) := by
  rw [wkU_smul]; rfl

/-- **Weakening by `ω`-variables**: `Γ ⊢ t : A` implies `Γ + ω Θ ⊢ t : A`. -/
theorem HasType.weaken_omega {m n : Nat} {Γ : Fin n → S.Ty m} {u : Fin n → Usage m}
    {t : Tm S m n} {A : S.Ty m} (h : HasType S Γ u t A) (θ : Fin n → Usage m) :
    HasType S Γ (u + (Usage.omega : Usage m) • θ) t A := by
  induction h with
  | var x v hu =>
    refine .var x (v + θ) ?_
    rw [hu, smul_add]; abel
  | lam _ ih =>
    refine .lam ?_
    have := ih (Fin.cons 0 θ)
    rwa [smul_cons, cons_add_cons, mul_zero, add_zero] at this
  | app h₁ h₂ hu ih₁ _ =>
    refine .app (ih₁ θ) h₂ ?_
    rw [hu]; abel
  | mlam _ ih =>
    refine .mlam ?_
    have := ih (wkU θ)
    rw [omega_smul_wkU] at this
    convert this using 1
    funext x; simp [wkU]
  | mapp _ ih => exact .mapp (ih θ)
  | con v w hargs hu _ =>
    refine .con (v + θ) w hargs ?_
    rw [hu, smul_add]; abel
  | @case m n Γ u u₁ u₂ π t d ps brs C ht hbrs hu _ ih =>
    refine .case ht (u₂ := u₂ + (Usage.omega : Usage m) • θ) (fun k => ?_) ?_
    · have := ih k (Fin.append θ 0)
      rwa [smul_append, append_add_append, smul_zero, add_zero] at this
    · rw [hu]; abel
  | @lett m n Γ u u₂ π j tys rhs body C w hrhs hbody hu _ ih =>
    refine .lett (u₂ := u₂ + (Usage.omega : Usage m) • θ) w hrhs ?_ ?_
    · have := ih (Fin.append θ 0)
      rwa [smul_append, append_add_append, smul_zero, add_zero] at this
    · rw [hu]; abel

theorem renU_liftR {m n n' : Nat} (ρ : Fin n → Fin n') (a : Usage m) (u : Fin n → Usage m) :
    mix (fun x => Pi.single (liftR ρ x) 1) (Fin.cons a u) =
      Fin.cons a (mix (fun x => Pi.single (ρ x) 1) u) := by
  rw [← mix_cons]
  congr 1
  funext x
  refine Fin.cases ?_ (fun y => ?_) x
  · rfl
  · simp only [liftR, Fin.cases_succ, Fin.cons_succ]
    exact single_succ_eq_cons _

theorem renU_liftRN {m n n' : Nat} (j : Nat) (ρ : Fin n → Fin n') (u : Fin n → Usage m)
    (f : Fin j → Usage m) :
    mix (fun x => Pi.single (liftRN j ρ x) 1) (Fin.append u f) =
      Fin.append (mix (fun x => Pi.single (ρ x) 1) u) f := by
  rw [← mix_append]
  congr 1
  funext x
  refine Fin.addCases (fun y => ?_) (fun y => ?_) x
  · simp only [liftRN, Fin.addCases_left, Fin.append_left]
    exact single_castAdd _
  · simp only [liftRN, Fin.addCases_right, Fin.append_right]

/-- **Renaming**: if `Γ ⊢ t : A` and `ρ` maps each variable to a variable of the same type, then
`t` renamed along `ρ` is well typed, with the multiplicities pushed forward along `ρ`. -/
theorem HasType.rename {m n : Nat} {Γ : Fin n → S.Ty m} {u : Fin n → Usage m}
    {t : Tm S m n} {A : S.Ty m} (h : HasType S Γ u t A) {n' : Nat} (ρ : Fin n → Fin n')
    (Δ : Fin n' → S.Ty m) (hΔ : ∀ x, Δ (ρ x) = Γ x) :
    HasType S Δ (mix (fun x => Pi.single (ρ x) 1) u) (t.rename ρ) A := by
  induction h generalizing n' with
  | var x v hu =>
    rw [← hΔ x]
    exact .var (ρ x) (mix (fun x => Pi.single (ρ x) 1) v) (by rw [hu, mix_omega_single_sum])
  | @lam m n Γ u π A' B t _ ih =>
    refine .lam ?_
    have := ih (liftR ρ) (Fin.cons A' Δ) (fun x => by
      refine Fin.cases ?_ (fun y => ?_) x
      · rfl
      · simp [liftR, hΔ])
    rwa [renU_liftR] at this
  | app _ _ hu ih₁ ih₂ =>
    exact .app (ih₁ ρ Δ hΔ) (ih₂ ρ Δ hΔ) (by rw [hu, mix_add, mix_smul])
  | @mlam m n Γ u t A _ ih =>
    refine .mlam ?_
    have := ih ρ (fun x => (Δ x).wk) (fun x => by simp [hΔ])
    have e := wkU_mix (fun x => Pi.single (ρ x) (1 : Usage _)) u
    simp only [wkU_single] at e
    convert this using 1
  | mapp _ ih => exact .mapp (ih ρ Δ hΔ)
  | con v w _ hu ih =>
    refine .con (mix (fun x => Pi.single (ρ x) 1) v) (fun i => mix (fun x => Pi.single (ρ x) 1) (w i)) (fun i => ih i ρ Δ hΔ) ?_
    rw [hu, mix_add, mix_smul, mix_sum]
    simp only [mix_smul]
  | @case m n Γ u u₁ u₂ π t d ps brs C _ _ hu ih₁ ih =>
    refine .case (u₂ := mix (fun x => Pi.single (ρ x) 1) u₂) (ih₁ ρ Δ hΔ) (fun k => ?_) (by rw [hu, mix_add, mix_smul])
    have := ih k (liftRN _ ρ) (Fin.append Δ (fun i => (S.fieldTy d k i).subst ps)) (fun x => by
      refine Fin.addCases (fun y => ?_) (fun y => ?_) x
      · simp [liftRN, hΔ]
      · simp [liftRN])
    rwa [renU_liftRN] at this
  | @lett m n Γ u u₂ π j tys rhs body C w _ _ hu ih₁ ih =>
    refine .lett (u₂ := mix (fun x => Pi.single (ρ x) 1) u₂) (fun i => mix (fun x => Pi.single (ρ x) 1) (w i)) (fun i => ih₁ i ρ Δ hΔ) ?_
      (by rw [hu, mix_add, mix_smul, mix_sum])
    have := ih (liftRN j ρ) (Fin.append Δ tys) (fun x => by
      refine Fin.addCases (fun y => ?_) (fun y => ?_) x
      · simp [liftRN, hΔ]
      · simp [liftRN])
    rwa [renU_liftRN] at this
-- [NOT IN PAPER ◀ END]

end LH
