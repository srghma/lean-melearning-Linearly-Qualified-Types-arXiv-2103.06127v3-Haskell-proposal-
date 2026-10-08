module

public import RequestProject.LH.MSubst

/-!
# The substitution lemma for `λq→`

No counterpart in the paper (whose metatheory, in its Appendix A, is not part of the supplied
text).  `HasType.subst` is the linear substitution lemma, in parallel form: if
`Γ ⊢ t : A` with multiplicities `u`, and each variable `x` is replaced by a term `σ x` with
`Δ ⊢ σ x : Γ x` with multiplicities `w x`, then `Δ ⊢ t[σ] : A` with multiplicities
`Σₓ u x • w x`: a variable used `π` times contributes `π` times the multiplicities of the term
that replaces it.  `HasType.subst_one` is the familiar special case
`Γ, x :_π A ⊢ t : B` and `Δ ⊢ s : A` imply `Γ + π Δ ⊢ t[s/x] : B`.
-/

@[expose] public section

namespace LH

variable {S : Sig}

-- [NOT IN PAPER ▶ START] substitution lemma
/-- **Substitution lemma** (parallel form). -/
theorem HasType.subst {m n : Nat} {Γ : Fin n → S.Ty m} {u : Fin n → Usage m}
    {t : Tm S m n} {A : S.Ty m} (h : HasType S Γ u t A) {n' : Nat} (σ : Fin n → Tm S m n')
    (Δ : Fin n' → S.Ty m) (w : Fin n → Fin n' → Usage m)
    (hσ : ∀ x, HasType S Δ (w x) (σ x) (Γ x)) :
    HasType S Δ (mix w u) (t.subst σ) A := by
  induction h generalizing n' with
  | var x v hu =>
    have := (hσ x).weaken_omega (mix w v)
    rw [hu, mix_omega_single_sum, add_comm]
    exact this
  | @lam m n Γ u π A' B t _ ih =>
    refine .lam ?_
    have := ih (Tm.liftσ σ) (Fin.cons A' Δ)
      (Fin.cons (Pi.single 0 1) (fun x => Fin.cons 0 (w x))) (fun x => by
        refine Fin.cases ?_ (fun y => ?_) x
        · exact .var 0 0 (by simp)
        · have := (hσ y).rename Fin.succ (Fin.cons A' Δ) (fun _ => rfl)
          rw [mix_single_succ] at this
          exact this)
    rwa [mix_cons] at this
  | app _ _ hu ih₁ ih₂ =>
    exact .app (ih₁ σ Δ w hσ) (ih₂ σ Δ w hσ) (by rw [hu, mix_add, mix_smul])
  | @mlam m n Γ u t A _ ih =>
    refine .mlam ?_
    have := ih (fun x => (σ x).mwk) (fun x => (Δ x).wk) (fun x => wkU (w x))
      (fun x => (hσ x).msubst (fun i => Mult.var i.succ))
    have e : (fun x => Usage.wk (mix w u x)) = mix (fun x => wkU (w x)) (fun x => Usage.wk (u x)) :=
      wkU_mix w u
    rw [e]
    exact this
  | mapp _ ih => exact .mapp (ih σ Δ w hσ)
  | con v w' _ hu ih =>
    refine .con (mix w v) (fun i => mix w (w' i)) (fun i => ih i σ Δ w hσ) ?_
    rw [hu, mix_add, mix_smul, mix_sum]
    simp only [mix_smul]
  | @case m n Γ u u₁ u₂ π t d ps brs C _ _ hu ih₁ ih =>
    refine .case (u₂ := mix w u₂) (ih₁ σ Δ w hσ) (fun k => ?_) (by rw [hu, mix_add, mix_smul])
    have := ih k (Tm.liftσN _ σ) (Fin.append Δ (fun i => (S.fieldTy d k i).subst ps))
      (Fin.append (fun x => Fin.append (w x) 0) (fun i => Pi.single (Fin.natAdd n' i) 1))
      (fun x => by
        refine Fin.addCases (fun y => ?_) (fun y => ?_) x
        · simp only [Tm.liftσN, Fin.addCases_left, Fin.append_left]
          have := (hσ y).rename (Fin.castAdd _)
            (Fin.append Δ (fun i => (S.fieldTy d k i).subst ps)) (fun _ => by simp)
          rwa [mix_single_castAdd] at this
        · simp only [Tm.liftσN, Fin.addCases_right, Fin.append_right]
          have := HasType.var (S := S)
            (Γ := Fin.append Δ (fun i => (S.fieldTy d k i).subst ps)) (Fin.natAdd n' y) 0
            (u := Pi.single (Fin.natAdd n' y) 1) (by simp)
          rwa [Fin.append_right] at this)
    rwa [mix_append] at this
  | @lett m n Γ u u₂ π j tys rhs body C w' _ _ hu ih₁ ih =>
    refine .lett (u₂ := mix w u₂) (fun i => mix w (w' i)) (fun i => ih₁ i σ Δ w hσ) ?_
      (by rw [hu, mix_add, mix_smul, mix_sum])
    have := ih (Tm.liftσN j σ) (Fin.append Δ tys)
      (Fin.append (fun x => Fin.append (w x) 0) (fun i => Pi.single (Fin.natAdd n' i) 1))
      (fun x => by
        refine Fin.addCases (fun y => ?_) (fun y => ?_) x
        · simp only [Tm.liftσN, Fin.addCases_left, Fin.append_left]
          have := (hσ y).rename (Fin.castAdd j) (Fin.append Δ tys) (fun _ => by simp)
          rwa [mix_single_castAdd] at this
        · simp only [Tm.liftσN, Fin.addCases_right, Fin.append_right]
          have := HasType.var (S := S) (Γ := Fin.append Δ tys) (Fin.natAdd n' y) 0
            (u := Pi.single (Fin.natAdd n' y) 1) (by simp)
          rwa [Fin.append_right] at this)
    rwa [mix_append] at this

/-- **Substitution lemma** for one variable: from `Γ, x :_π A ⊢ t : B` and `Δ ⊢ s : A` infer
`Γ + π Δ ⊢ t[s/x] : B`. -/
theorem HasType.subst_one {m n : Nat} {Γ : Fin n → S.Ty m} {u v : Fin n → Usage m}
    {π : Usage m} {A B : S.Ty m} {t : Tm S m (n + 1)} {s : Tm S m n}
    (ht : HasType S (Fin.cons A Γ) (Fin.cons π u) t B) (hs : HasType S Γ v s A) :
    HasType S Γ (u + π • v) (t.subst (Fin.cons s Tm.var)) B := by
  have := ht.subst (Fin.cons s Tm.var) Γ (Fin.cons v (fun x => Pi.single x 1)) (fun x => by
    refine Fin.cases ?_ (fun y => ?_) x
    · exact hs
    · exact .var y 0 (by simp))
  unfold mix at this
  rw [Fin.sum_univ_succ] at this
  simp only [Fin.cons_zero, Fin.cons_succ] at this
  have e : ∑ x : Fin n, u x • (Pi.single x (1 : Usage m) : Fin n → Usage m) = u :=
    mix_single_self u
  rw [e, add_comm] at this
  exact this
-- [NOT IN PAPER ◀ END]

end LH
