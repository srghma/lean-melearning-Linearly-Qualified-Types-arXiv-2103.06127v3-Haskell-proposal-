module

public import RequestProject.LQT.DesugarTypingAux

/-!
# Correctness of desugaring (Theorem 7.1)

Paper location: §7.2.3 "Translating terms", Theorem 7.1 "Desugaring" (the paper only says
that it is "straightforward by induction").  The start and end of each part is marked by
`-- [PAPER ▶ START]` / `-- [PAPER ◀ END]` comments.

If `Q ; Γ ⊢ e : τ` (derivation `d`) then `⟦Γ⟧, z :₁ ⟦Q⟧ ⊢ ⟦d⟧_z : ⟦τ⟧` in the core calculus.
-/

@[expose] public section

namespace LQT

open Function SConstr

variable {P : Type}

-- [PAPER ▶ START] §7.2.3 › Theorem 7.1 "Desugaring": the induction behind the theorem, generalised
--   to an arbitrary placement of the variables (the paper's "straightforward by induction")
/-- **Desugaring is type-correct**, generalised form: for any placement of the variables of
`Γ` along an injective renaming `ρ` into a core context `Γ'`, and of the evidence variable at
`z`, the desugaring is well typed. -/
theorem desugarAt_typed {D : LDomain (Atom P)} (hD : D.Lawful) {sig : DataSig P} {k n : Nat}
    {Q : SConstr (Atom P k)} {Γ : Fin n → Scheme P k} {u : Fin n → Usage} {e : Tm sig k n}
    {τ : Ty P k} (d : HasType D sig Q Γ u e τ) :
    ∀ {m : Nat} {Γ' : Fin m → CScheme P k} {ρ : Fin n → Fin m} {z : Fin m}, Injective ρ →
      (∀ i, Γ' (ρ i) = (Γ i).ds) → (∀ i, ρ i ≠ z) → Γ' z = CScheme.mono (.ev Q) →
      CHasType D sig Γ' (push ρ u + single z) (desugarAt d ρ z) τ.ds := by
  induction d with
  | @var k n Γ x σ v τs hx =>
    intro m Γ' ρ z hρ hΓ hz hev
    have hxt : Γ' (ρ x) = σ.ds := by rw [hΓ, hx]
    have h2 := CHasType.var (D := D) (sig := sig) (Γ := Γ') (x := ρ x) (σ := σ.ds) (push ρ v)
      τs hxt
    by_cases hQ : σ.Q = 0
    · simp only [desugarAt, hQ, if_true]
      refine (CHasType.letUnit (.prim .drop (var_ev (hev.trans (by simp [hQ, tsubst]))))
        (h2.cast rfl (by simp [Scheme.ds, hQ, Ty.ds_subst]))).cast ?_ rfl
      simp [push_add hρ, push_smul hρ, push_single hρ]; abel
    · simp only [desugarAt, hQ, if_false]
      refine (CHasType.app (π := .one) (h2.cast rfl
        (by simp [Scheme.ds, hQ, Ty.ds_subst, CTy.subst])) (var_ev hev)).cast ?_ rfl
      simp [push_add hρ, push_smul hρ, push_single hρ]
  | @con k n Γ v T i τs =>
    intro m Γ' ρ z hρ hΓ hz hev
    simp only [desugarAt]
    refine (CHasType.letUnit (.prim .drop (var_ev hev)) (CHasType.con (push ρ v) T i τs)).cast
      ?_ rfl
    simp [push_smul hρ]; abel
  | @lam k n Q Γ u π τ₁ τ₂ e d ih =>
    intro m Γ' ρ z hρ hΓ hz hev
    simp only [desugarAt]
    have h := ih (Γ' := Fin.cons (CScheme.mono τ₁.ds) Γ') (ρ := liftR ρ) (z := z.succ)
      (liftR_injective hρ)
      (by intro i; cases i using Fin.cases <;> simp [hΓ])
      (by intro i; cases i using Fin.cases <;> simp [hz, (Fin.succ_ne_zero _).symm])
      (by simpa using hev)
    refine CHasType.lam (h.cast ?_ rfl)
    simp [push_liftR hρ, single_succ_eq, cons_add_cons]
  | @app k n Q₁ Q₂ Γ u₁ u₂ π τ₁ τ e₁ e₂ d₁ d₂ ih₁ ih₂ =>
    intro m Γ' ρ z hρ hΓ hz hev
    have hs : CHasType D sig Γ' (single z) (.prim (.split Q₁ (π • Q₂)) (.var z))
        (.tensor (.ev Q₁) (.ev (π • Q₂))) := .prim (.split _ _) (var_ev hev)
    cases π with
    | one =>
      simp only [desugarAt]
      have h₁ := ih₁ (Γ' := Fin.cons (CScheme.mono (CTy.ev Q₁))
          (Fin.cons (CScheme.mono (CTy.ev ((Mult.one : Mult) • Q₂))) Γ'))
        (ρ := shift (shift ρ)) (z := 0) (shift_injective (shift_injective hρ))
        (by intro i; simp [hΓ]) (by intro i; simp) rfl
      have h₂ := ih₂ (Γ' := Fin.cons (CScheme.mono (CTy.ev Q₁))
          (Fin.cons (CScheme.mono (CTy.ev ((Mult.one : Mult) • Q₂))) Γ'))
        (ρ := shift (shift ρ)) (z := Fin.succ 0) (shift_injective (shift_injective hρ))
        (by intro i; simp [hΓ])
        (by intro i h; have := congrArg Fin.val h; simp at this) (by simp)
      refine (CHasType.letPair hs ((CHasType.app h₁ h₂).cast
        (u' := Fin.cons Usage.one (Fin.cons Usage.one (push ρ (u₁ + (Mult.one : Mult) • u₂))))
        ?_ rfl)).cast ?_ rfl
      · simp [push_add, push_shift, shift_injective, hρ, single_zero_eq,
          single_one_eq, cons_add_cons]
      · simp; abel
    | omega =>
      simp only [desugarAt]
      have hρ2 := shift_injective (shift_injective hρ)
      have hρ3 := shift_injective hρ2
      have h₁ := ih₁ (Γ' := Fin.cons (CScheme.mono (CTy.ev ((Mult.omega : Mult) • Q₂)))
          (Fin.cons (CScheme.mono (CTy.ev Q₁))
            (Fin.cons (CScheme.mono (CTy.ev ((Mult.omega : Mult) • Q₂))) Γ')))
        (ρ := shift (shift (shift ρ))) (z := Fin.succ 0) hρ3
        (by intro i; simp [hΓ])
        (by intro i h; have := congrArg Fin.val h; simp at this) rfl
      have h₂ := ih₂ (Γ' := Fin.cons (CScheme.mono (CTy.ev Q₂))
          (Fin.cons (CScheme.mono (CTy.ev ((Mult.omega : Mult) • Q₂)))
          (Fin.cons (CScheme.mono (CTy.ev Q₁))
            (Fin.cons (CScheme.mono (CTy.ev ((Mult.omega : Mult) • Q₂))) Γ'))))
        (ρ := shift (shift (shift (shift ρ)))) (z := 0) (shift_injective hρ3)
        (by intro i; simp [hΓ]) (by intro i; simp) rfl
      have hl := CHasType.let_ (π := .one)
        (CHasType.prim (.coe ((hD.lawful k).omega_smul_entails Q₂)) (var_ev (z := 0) rfl))
        (h₂.cast
          (u' := Fin.cons (Usage.ofMult .one) (push (shift (shift (shift ρ))) u₂))
          (by simp [push_shift hρ3, single_zero_eq, cons_add_cons]) rfl)
      have ha := CHasType.app h₁ hl
      have hu := CHasType.prim (u := single (Fin.succ 0)) (.urEv Q₂)
        (var_ev (D := D) (sig := sig) (Γ' := Fin.cons (CScheme.mono (CTy.ev Q₁))
          (Fin.cons (CScheme.mono (CTy.ev ((Mult.omega : Mult) • Q₂))) Γ'))
          (z := Fin.succ 0) rfl)
      have hlu := CHasType.letUr hu (ha.cast
        (u' := Fin.cons Usage.omega (push (shift (shift ρ)) u₁ + single 0 +
          (Mult.omega : Mult) • push (shift (shift ρ)) u₂)) ?_ rfl)
      · refine (CHasType.letPair hs (hlu.cast
          (u' := Fin.cons Usage.one (Fin.cons Usage.one
            (push ρ (u₁ + (Mult.omega : Mult) • u₂)))) ?_ rfl)).cast ?_ rfl
        · simp [push_add, push_smul, push_shift, shift_injective, hρ, single_zero_eq,
            single_one_eq, cons_add_cons, smul_cons]
        · abel
      · simp [push_shift, shift_injective, hρ, hρ2, single_zero_eq,
          single_one_eq, cons_add_cons, smul_cons]
  | @pack k n j m' Q Γ u τ mul pred ar args e υs d ih =>
    intro m Γ' ρ z hρ hΓ hz hev
    simp only [desugarAt]
    have hρ2 := shift_injective (shift_injective hρ)
    have h := ih (Γ' := Fin.cons (CScheme.mono (CTy.ev Q))
        (Fin.cons (CScheme.mono (CTy.ev ((exqC m' mul pred ar args).tsubst (instSub υs)))) Γ'))
      (ρ := shift (shift ρ)) (z := 0) hρ2 (by intro i; simp [hΓ]) (by intro i; simp) rfl
    have hp := CHasType.pack (τ := τ.ds) (υ := CTy.ev (exqC m' mul pred ar args)) υs
      (h.cast rfl (Ty.ds_subst _ _))
      (var_ev (D := D) (sig := sig)
        (Γ' := Fin.cons (CScheme.mono (CTy.ev Q))
          (Fin.cons (CScheme.mono (CTy.ev ((exqC m' mul pred ar args).tsubst (instSub υs)))) Γ'))
        (z := Fin.succ 0) rfl)
    refine (CHasType.letPair (.prim (.split _ _) (var_ev hev)) (hp.cast
      (u' := Fin.cons Usage.one (Fin.cons Usage.one (push ρ u))) ?_ rfl)).cast ?_ rfl
    · simp [push_shift, shift_injective, hρ, single_zero_eq, single_one_eq,
        cons_add_cons]
    · abel
  | @unpack k n j m' Q₁ Q₂ Γ u₁ u₂ τ₁ mul pred ar args τ e₁ e₂ d₁ d₂ ih₁ ih₂ =>
    intro m Γ' ρ z hρ hΓ hz hev
    simp only [desugarAt]
    have hρ2 := shift_injective (shift_injective hρ)
    have hρ3 := shift_injective hρ2
    have hρ4 := shift_injective hρ3
    have hρ5 := shift_injective hρ4
    have h₁ := ih₁ (Γ' := Fin.cons (CScheme.mono (CTy.ev Q₁))
        (Fin.cons (CScheme.mono (CTy.ev Q₂)) Γ'))
      (ρ := shift (shift ρ)) (z := 0) hρ2 (by intro i; simp [hΓ]) (by intro i; simp) rfl
    have h₂ := ih₂ (Γ' := Fin.cons (CScheme.mono τ₁.ds)
        (Fin.cons (CScheme.mono (CTy.ev (Q₂.wk j + exqC m' mul pred ar args)))
        (Fin.cons (CScheme.mono τ₁.ds)
        (Fin.cons (CScheme.mono (CTy.ev (exqC m' mul pred ar args)))
        (cctxWk j (Fin.cons (CScheme.mono (CTy.ev Q₁))
          (Fin.cons (CScheme.mono (CTy.ev Q₂)) Γ')))))))
      (ρ := liftR (shift (shift (shift (shift (shift ρ)))))) (z := Fin.succ 0)
      (liftR_injective hρ5)
      (by
        intro i
        cases i using Fin.cases with
        | zero => simp
        | succ i => simpa using cctxWk_ds j hΓ i)
      (by intro i; cases i using Fin.cases <;> simp only [liftR_zero, liftR_succ, shift_apply,
          ne_eq, Fin.ext_iff, Fin.val_succ, Fin.val_zero] <;> omega) rfl
    have hv1 := var_ev (D := D) (sig := sig) (Γ' := Fin.cons (CScheme.mono τ₁.ds)
        (Fin.cons (CScheme.mono (CTy.ev (exqC m' mul pred ar args)))
        (cctxWk j (Fin.cons (CScheme.mono (CTy.ev Q₁))
          (Fin.cons (CScheme.mono (CTy.ev Q₂)) Γ'))))) (z := Fin.succ 0) rfl
    have hv3 := var_ev (D := D) (sig := sig) (Γ' := Fin.cons (CScheme.mono τ₁.ds)
        (Fin.cons (CScheme.mono (CTy.ev (exqC m' mul pred ar args)))
        (cctxWk j (Fin.cons (CScheme.mono (CTy.ev Q₁))
          (Fin.cons (CScheme.mono (CTy.ev Q₂)) Γ')))))
        (z := Fin.succ (Fin.succ (Fin.succ 0))) (Q := Q₂.wk j)
        (by rw [Fin.cons_succ, Fin.cons_succ]; exact cctxWk_ev (x := Fin.succ 0) j rfl)
    have hj := CHasType.prim (.join (Q₂.wk j) (exqC m' mul pred ar args))
      (CHasType.pair hv3 hv1)
    have hx := CHasType.var_mono (D := D) (sig := sig)
      (Γ := Fin.cons (CScheme.mono (CTy.ev (Q₂.wk j + exqC m' mul pred ar args)))
        (Fin.cons (CScheme.mono τ₁.ds)
        (Fin.cons (CScheme.mono (CTy.ev (exqC m' mul pred ar args)))
        (cctxWk j (Fin.cons (CScheme.mono (CTy.ev Q₁))
          (Fin.cons (CScheme.mono (CTy.ev Q₂)) Γ'))))))
      (x := Fin.succ 0) 0 rfl
    have hl2 := CHasType.let_ (π := .one) hx (h₂.cast
      (u' := Fin.cons (Usage.ofMult .one) (push (shift (shift (shift (shift (shift ρ))))) u₂ +
        single 0)) (τ' := τ.ds.rename (Fin.castAdd j)) ?_ (by simp [Ty.wk, Ty.ds_rename]))
    · have hl1 := CHasType.let_ (π := .one) hj (hl2.cast
        (u' := Fin.cons (Usage.ofMult .one) (single 0 +
          push (shift (shift (shift (shift ρ)))) u₂)) ?_ rfl)
      · refine (CHasType.letPair (.prim (.split Q₁ Q₂) (var_ev hev)) ((CHasType.unpack h₁
          (hl1.cast (u' := Fin.cons Usage.one (Fin.cons Usage.one
            (single 1 + push (shift (shift ρ)) u₂))) ?_ rfl)).cast
          (u' := Fin.cons Usage.one (Fin.cons Usage.one (push ρ (u₁ + u₂)))) ?_ rfl)).cast ?_ rfl
        · simp [push_shift, shift_injective, hρ, hρ2, hρ3, single_zero_eq, single_succ_eq,
            single_one_eq, single_two_eq, cons_add_cons]
        · simp [push_add, push_shift, shift_injective, hρ, single_zero_eq,
            single_one_eq, cons_add_cons]
        · abel
      · simp [push_shift, shift_injective, hρ, hρ2, hρ3, hρ4, single_zero_eq,
          single_one_eq, cons_add_cons]
    · simp [push_liftR, push_shift, shift_injective, hρ, hρ2, hρ3, hρ4, hρ5, single_zero_eq,
        single_one_eq, cons_add_cons]
  | let_ d₁ d₂ ih₁ ih₂ =>
    intro m Γ' ρ z hρ hΓ hz hev
    exact dsLet_typed hD ih₁ ih₂ hρ hΓ hev
  | letSig d₁ d₂ ih₁ ih₂ =>
    intro m Γ' ρ z hρ hΓ hz hev
    exact dsLetSig_typed hD ih₁ ih₂ hρ hΓ hev
  | @case k n Q₁ Q₂ Γ u₁ u₂ π τ e T τs alts d ds ih ihs =>
    intro m Γ' ρ z hρ hΓ hz hev
    have hρ2 := shift_injective (shift_injective hρ)
    have hρ3 := shift_injective hρ2
    have hρ4 := shift_injective hρ3
    cases π with
    | one =>
      simp only [desugarAt]
      have h := ih (Γ' := Fin.cons (CScheme.mono (CTy.ev ((Mult.one : Mult) • Q₁)))
          (Fin.cons (CScheme.mono (CTy.ev Q₂)) Γ'))
        (ρ := shift (shift ρ)) (z := 0) hρ2 (by intro i; simp [hΓ]) (by intro i; simp)
        (by simp)
      have hs : ∀ i, CHasType D sig (caseCtxC sig
          (Fin.cons (CScheme.mono (CTy.ev ((Mult.one : Mult) • Q₁)))
            (Fin.cons (CScheme.mono (CTy.ev Q₂)) Γ')) T i τs)
          (caseUsage sig .one (push (shift (shift ρ)) u₂ + single 1) T i)
          (desugarAt (ds i) (liftRN _ (shift (shift ρ))) (Fin.natAdd _ (Fin.succ 0))) τ.ds := by
        intro i
        refine (ihs i (Γ' := caseCtxC sig
            (Fin.cons (CScheme.mono (CTy.ev ((Mult.one : Mult) • Q₁)))
              (Fin.cons (CScheme.mono (CTy.ev Q₂)) Γ')) T i τs) (z := Fin.natAdd _ (Fin.succ 0))
          (liftRN_injective _ hρ2) (caseCtxC_liftRN (by intro i; simp [hΓ]) T i τs)
          (liftRN_ne_natAdd (by intro i h; have := congrArg Fin.val h; simp at this))
          (by simp [caseCtxC])).cast ?_ rfl
        rw [push_caseUsage_add hρ2]; simp
      refine (CHasType.letPair (.prim (.split _ _) (var_ev hev)) ((CHasType.case h hs).cast
        (u' := Fin.cons Usage.one (Fin.cons Usage.one (push ρ ((Mult.one : Mult) • u₁ + u₂))))
          ?_ rfl)).cast ?_ rfl
      · simp [push_add, push_shift, shift_injective, hρ, single_zero_eq,
          single_one_eq, cons_add_cons]
      · abel
    | omega =>
      simp only [desugarAt]
      have h := ih (Γ' := Fin.cons (CScheme.mono (CTy.ev Q₁))
          (Fin.cons (CScheme.mono (CTy.ev ((Mult.omega : Mult) • Q₁)))
          (Fin.cons (CScheme.mono (CTy.ev ((Mult.omega : Mult) • Q₁)))
            (Fin.cons (CScheme.mono (CTy.ev Q₂)) Γ'))))
        (ρ := shift (shift (shift (shift ρ)))) (z := 0) hρ4 (by intro i; simp [hΓ])
        (by intro i; simp) rfl
      have hsc := CHasType.let_ (π := .one)
        (CHasType.prim (.coe ((hD.lawful k).omega_smul_entails Q₁)) (var_ev (z := 0) rfl))
        (h.cast
          (u' := Fin.cons (Usage.ofMult .one) (push (shift (shift (shift ρ))) u₁))
          (by simp [push_shift hρ3, single_zero_eq, cons_add_cons]) rfl)
      have hs : ∀ i, CHasType D sig (caseCtxC sig
          (Fin.cons (CScheme.mono (CTy.ev ((Mult.omega : Mult) • Q₁)))
          (Fin.cons (CScheme.mono (CTy.ev ((Mult.omega : Mult) • Q₁)))
            (Fin.cons (CScheme.mono (CTy.ev Q₂)) Γ'))) T i τs)
          (caseUsage sig .omega (push (shift (shift (shift ρ))) u₂ + single 2) T i)
          (desugarAt (ds i) (liftRN _ (shift (shift (shift ρ))))
            (Fin.natAdd _ (Fin.succ (Fin.succ 0)))) τ.ds := by
        intro i
        have hz3 : ∀ j, shift (shift (shift ρ)) j ≠ Fin.succ (Fin.succ 0) := by
          intro j
          simp only [shift_apply, ne_eq, Fin.ext_iff, Fin.val_succ, Fin.val_zero]
          omega
        refine (ihs i (Γ' := caseCtxC sig
            (Fin.cons (CScheme.mono (CTy.ev ((Mult.omega : Mult) • Q₁)))
            (Fin.cons (CScheme.mono (CTy.ev ((Mult.omega : Mult) • Q₁)))
              (Fin.cons (CScheme.mono (CTy.ev Q₂)) Γ'))) T i τs)
          (z := Fin.natAdd _ (Fin.succ (Fin.succ 0)))
          (liftRN_injective _ hρ3) (caseCtxC_liftRN (by intro i; simp [hΓ]) T i τs)
          (liftRN_ne_natAdd hz3)
          (by simp only [caseCtxC, Fin.append_right]; rfl)).cast ?_ rfl
        rw [push_caseUsage_add hρ3]; simp
      have hu := CHasType.prim (u := single 0) (.urEv Q₁)
        (var_ev (D := D) (sig := sig)
          (Γ' := Fin.cons (CScheme.mono (CTy.ev ((Mult.omega : Mult) • Q₁)))
            (Fin.cons (CScheme.mono (CTy.ev Q₂)) Γ')) (z := 0) rfl)
      refine (CHasType.letPair (.prim (.split _ _) (var_ev hev)) ((CHasType.letUr hu
        ((CHasType.case hsc hs).cast (u' := Fin.cons Usage.omega
          ((Mult.omega : Mult) • push (shift (shift ρ)) u₁ + push (shift (shift ρ)) u₂ + single 1))
          ?_ rfl)).cast
        (u' := Fin.cons Usage.one (Fin.cons Usage.one (push ρ ((Mult.omega : Mult) • u₁ + u₂))))
          ?_ rfl)).cast ?_ rfl
      · simp [push_shift, hρ2, single_zero_eq, single_one_eq, single_two_eq,
          cons_add_cons, smul_cons]
        abel
      · simp [push_add, push_smul, push_shift, shift_injective, hρ, single_zero_eq,
          single_one_eq, cons_add_cons, smul_cons]
      · abel
  | @sub k n Q Q₁ Γ u τ e d hent ih =>
    intro m Γ' ρ z hρ hΓ hz hev
    simp only [desugarAt]
    have h := ih (Γ' := Fin.cons (CScheme.mono (CTy.ev Q₁)) Γ') (ρ := shift ρ) (z := 0)
      (shift_injective hρ) (by intro i; simp [hΓ]) (by intro i; simp) rfl
    refine (CHasType.let_ (π := .one) (.prim (.coe hent) (var_ev hev)) (h.cast
      (u' := Fin.cons (Usage.ofMult .one) (push ρ u)) ?_ rfl)).cast ?_ rfl
    · simp [push_shift hρ, single_zero_eq, cons_add_cons]
    · simp; abel

-- [PAPER ◀ END] §7.2.3 › Theorem 7.1, induction

-- [NOT IN PAPER ▶ START] helper
lemma push_succ {n : Nat} (u : Fin n → Usage) : push Fin.succ u = Fin.cons 0 u :=
  push_eq (Fin.succ_injective _) (fun i => by simp) (fun j h => by
    cases j using Fin.cases with
    | zero => rfl
    | succ j' => exact absurd rfl (h j'))

-- [NOT IN PAPER ◀ END] helper

-- [PAPER ▶ START] §7.2.3 › Theorem 7.1 "Desugaring", as stated in the paper
/-- **Theorem 7.1 (desugaring preserves typing).**  If `Q ; Γ ⊢ e : τ` (derivation `d`), then
in the core calculus `⟦Γ⟧, z :₁ ⟦Q⟧ ⊢ ⟦d⟧_z : ⟦τ⟧`, where the evidence variable `z` is the
de Bruijn index `0` and the variables of `Γ` are shifted by one. -/
theorem desugar_typed {D : LDomain (Atom P)} (hD : D.Lawful) {sig : DataSig P} {k n : Nat}
    {Q : SConstr (Atom P k)} {Γ : Fin n → Scheme P k} {u : Fin n → Usage} {e : Tm sig k n}
    {τ : Ty P k} (d : HasType D sig Q Γ u e τ) :
    CHasType D sig (Fin.cons (CScheme.mono (.ev Q)) (fun i => (Γ i).ds)) (Fin.cons Usage.one u)
      (desugar d) τ.ds :=
  (desugarAt_typed hD d (Fin.succ_injective _) (fun _ => rfl) (fun i => Fin.succ_ne_zero i)
    rfl).cast (by rw [push_succ, single_zero_eq, cons_add_cons]; simp) rfl

-- [PAPER ◀ END] §7.2.3 › Theorem 7.1

end LQT
