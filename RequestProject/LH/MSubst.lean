module

public import RequestProject.LH.Weakening

/-!
# Substitution of multiplicities in typing derivations

No counterpart in the paper.  `HasType.msubst` : if `Γ ⊢ t : A` then `Γ[s] ⊢ t[s] : A[s]` for
every substitution `s` of multiplicities for multiplicity variables.  It is used for the
reduction `(λp. t) π ⟶ t[π/p]`.
-/

@[expose] public section

namespace LH

variable {S : Sig}

-- [NOT IN PAPER ▶ START] substitution of multiplicities in derivations
section substU
variable {m m' n : Nat} (s : Fin m → Mult m')

/-- Substitution of multiplicities in a usage vector. -/
def substU (u : Fin n → Usage m) : Fin n → Usage m' := fun x => Usage.subst s (u x)

theorem substU_add (u v : Fin n → Usage m) : substU s (u + v) = substU s u + substU s v := by
  funext x; simp [substU]

theorem substU_smul (c : Usage m) (u : Fin n → Usage m) :
    substU s (c • u) = Usage.subst s c • substU s u := by
  funext x; simp [substU]

theorem substU_sum {ι : Type} [Fintype ι] (f : ι → Fin n → Usage m) :
    substU s (∑ i, f i) = ∑ i, substU s (f i) := by
  funext x; simp [substU, Finset.sum_apply, map_sum]

theorem substU_single (x : Fin n) : substU s (Pi.single x (1 : Usage m)) = Pi.single x 1 := by
  funext y; by_cases h : y = x
  · subst h; simp [substU]
  · simp [substU, h]

theorem substU_cons (a : Usage m) (u : Fin n → Usage m) :
    substU s (Fin.cons a u : Fin (n + 1) → Usage m) = Fin.cons (Usage.subst s a) (substU s u) := by
  funext y; refine Fin.cases ?_ (fun z => ?_) y <;> rfl

theorem substU_append {j : Nat} (u : Fin n → Usage m) (f : Fin j → Usage m) :
    substU s (Fin.append u f) = Fin.append (substU s u) (fun i => Usage.subst s (f i)) := by
  funext y; refine Fin.addCases (fun z => ?_) (fun z => ?_) y <;> simp [substU]

theorem substTy_cons (A : S.Ty m) (Γ : Fin n → S.Ty m) :
    (fun x => ((Fin.cons A Γ : Fin (n + 1) → S.Ty m) x).subst s) =
      Fin.cons (A.subst s) (fun x => (Γ x).subst s) := by
  funext y; refine Fin.cases ?_ (fun z => ?_) y <;> rfl

theorem substTy_append {j : Nat} (Γ : Fin n → S.Ty m) (f : Fin j → S.Ty m) :
    (fun x => (Fin.append Γ f x).subst s) =
      Fin.append (fun x => (Γ x).subst s) (fun i => (f i).subst s) := by
  funext y; refine Fin.addCases (fun z => ?_) (fun z => ?_) y <;> simp

end substU

theorem fieldTy_subst_subst {m m' : Nat} (s : Fin m → Mult m') {d : S.Dn} (k : Fin (S.ncons d))
    (i : Fin (S.arity d k)) (ps : Fin (S.np d) → Mult m) :
    ((S.fieldTy d k i).subst ps).subst s = (S.fieldTy d k i).subst (fun l => (ps l).subst s) :=
  Ty.subst_subst _ _ _

/-- **Substitution of multiplicities**: `Γ ⊢ t : A` implies `Γ[s] ⊢ t[s] : A[s]`. -/
theorem HasType.msubst {m n : Nat} {Γ : Fin n → S.Ty m} {u : Fin n → Usage m}
    {t : Tm S m n} {A : S.Ty m} (h : HasType S Γ u t A) {m' : Nat} (s : Fin m → Mult m') :
    HasType S (fun x => (Γ x).subst s) (substU s u) (t.msubst s) (A.subst s) := by
  induction h generalizing m' with
  | var x v hu =>
    exact .var x (substU s v) (by rw [hu, substU_add, substU_smul, substU_single]; rfl)
  | lam _ ih =>
    have := ih s
    rw [substTy_cons, substU_cons] at this
    exact .lam this
  | app _ _ hu ih₁ ih₂ =>
    exact .app (ih₁ s) (ih₂ s) (by rw [hu, substU_add, substU_smul]; rfl)
  | @mlam m n Γ u t A _ ih =>
    have := ih (Mult.liftS s)
    refine .mlam ?_
    convert this using 1
    · funext x; exact (Ty.subst_liftS_wk s (Γ x)).symm
    · funext x; exact (Usage.subst_liftS_wk s (u x)).symm
  | @mapp m n Γ u t A π _ ih =>
    have := (ih s).mapp (π := π.subst s)
    rwa [← Ty.subst_inst] at this
  | @con m n Γ u d k args ps v w _ hu ih =>
    refine .con (ps := fun l => (ps l).subst s) (substU s v) (fun i => substU s (w i))
      (fun i => ?_) ?_
    · have := ih i s
      rwa [fieldTy_subst_subst] at this
    · rw [hu, substU_add, substU_smul, substU_sum]
      simp only [substU_smul, Usage.subst_nz, Mult.subst_subst]
      rfl
  | @case m n Γ u u₁ u₂ π t d ps brs C _ _ hu ih₁ ih =>
    refine .case (ps := fun l => (ps l).subst s) (u₂ := substU s u₂) (ih₁ s) (fun k => ?_)
      (by rw [hu, substU_add, substU_smul]; rfl)
    have := ih k s
    rw [substTy_append, substU_append] at this
    simp only [fieldTy_subst_subst, Usage.subst_nz, Mult.subst_mul, Mult.subst_subst] at this
    exact this
  | @lett m n Γ u u₂ π j tys rhs body C w _ _ hu ih₁ ih =>
    refine .lett (u₂ := substU s u₂) (fun i => substU s (w i)) (fun i => ih₁ i s) ?_
      (by rw [hu, substU_add, substU_smul, substU_sum]; rfl)
    have := ih s
    rw [substTy_append, substU_append] at this
    exact this
-- [NOT IN PAPER ◀ END]

end LH
