module

public import RequestProject.LQT.Desugar

/-!
# Correctness of desugaring: auxiliary lemmas

Usage-vector arithmetic and the typing of the translations of `let`-bindings, used in the
proof of Theorem 7.1 (`RequestProject/LQT/DesugarTyping.lean`).

Paper location: none.  The paper proves Theorem 7.1 (§7.2.3) with "It is straightforward, by
induction"; this whole file consists of auxiliary lemmas for that induction.
-/

@[expose] public section

namespace LQT

open Function SConstr

-- [NOT IN PAPER ▶ START] auxiliary lemmas for the proof of Theorem 7.1 (whole file)
variable {P : Type}

local notation "ω•" Q => ((Mult.omega : Mult) • Q)

@[simp] lemma Mult.one_smul_any {M : Type*} [MulAction Mult M] (x : M) :
    (Mult.one : Mult) • x = x :=
  one_smul Mult x

lemma single_one_eq {n : Nat} :
    (single 1 : Fin (n + 1 + 1) → Usage) = Fin.cons 0 (single 0) := by
  simpa using single_succ_eq (0 : Fin (n + 1))

lemma single_two_eq {n : Nat} :
    (single 2 : Fin (n + 1 + 1 + 1) → Usage) = Fin.cons 0 (single 1) := by
  simpa using single_succ_eq (1 : Fin (n + 1 + 1))

/-- An evidence variable. -/
lemma var_ev {D : LDomain (Atom P)} {sig : DataSig P} {k m : Nat} {Γ' : Fin m → CScheme P k}
    {z : Fin m} {Q : SConstr (Atom P k)} (hev : Γ' z = CScheme.mono (.ev Q)) :
    CHasType D sig Γ' (single z) (.var z) (.ev Q) :=
  (CHasType.var_mono 0 hev).cast (by simp) rfl

lemma push_caseUsage_add {sig : DataSig P} {n m : Nat} {ρ : Fin n → Fin m} (hρ : Injective ρ)
    (π : Mult) (u : Fin n → Usage) (z : Fin m) (T : Nat) (i : Fin (sig.ncons T)) :
    push (liftRN (sig.arity T i) ρ) (caseUsage sig π u T i) + single (Fin.natAdd _ z) =
      caseUsage sig π (push ρ u + single z) T i := by
  simp only [caseUsage, push_liftRN _ hρ, single_natAdd, append_add_append, add_zero]

lemma caseCtxC_liftRN {sig : DataSig P} {k n m : Nat} {ρ : Fin n → Fin m}
    {Γ : Fin n → Scheme P k} {Γ' : Fin m → CScheme P k} (hΓ : ∀ i, Γ' (ρ i) = (Γ i).ds)
    (T : Nat) (i : Fin (sig.ncons T)) (τs : Fin (sig.params T) → Ty P k)
    (j : Fin (sig.arity T i + n)) :
    caseCtxC sig Γ' T i τs (liftRN _ ρ j) = (caseCtx sig Γ T i τs j).ds := by
  refine Fin.addCases (fun j' => ?_) (fun j' => ?_) j
  · simp [caseCtxC, caseCtx]
  · simp [caseCtxC, caseCtx, hΓ]

lemma liftRN_ne_natAdd {k n m : Nat} {ρ : Fin n → Fin m} {z : Fin m} (hz : ∀ i, ρ i ≠ z)
    (j : Fin (k + n)) : liftRN k ρ j ≠ Fin.natAdd k z := by
  refine Fin.addCases (fun j' => ?_) (fun j' => ?_) j
  · simp only [liftRN_castAdd, ne_eq, Fin.ext_iff, Fin.val_castAdd, Fin.val_natAdd]; omega
  · simpa [Fin.ext_iff] using hz j'

/-- Typing of the translation of `let`-bindings without signature. -/
theorem dsLet_typed {D : LDomain (Atom P)} (hD : D.Lawful) {sig : DataSig P} {k n : Nat}
    {π : Mult} {Q Q₁ Q₂ : SConstr (Atom P k)} {Γ : Fin n → Scheme P k} {u₁ u₂ : Fin n → Usage}
    {τ₁ τ : Ty P k}
    {t₁ : ∀ {m' : Nat}, (Fin n → Fin m') → Fin m' → CTm sig k m'}
    {t₂ : ∀ {m' : Nat}, (Fin (n + 1) → Fin m') → Fin m' → CTm sig k m'}
    (ht₁ : ∀ {m' : Nat} {Γ'' : Fin m' → CScheme P k} {ρ' : Fin n → Fin m'} {z' : Fin m'},
      Injective ρ' → (∀ i, Γ'' (ρ' i) = (Γ i).ds) → (∀ i, ρ' i ≠ z') →
      Γ'' z' = CScheme.mono (.ev (Q₁ + Q)) →
      CHasType D sig Γ'' (push ρ' u₁ + single z') (t₁ ρ' z') τ₁.ds)
    (ht₂ : ∀ {m' : Nat} {Γ'' : Fin m' → CScheme P k} {ρ' : Fin (n + 1) → Fin m'} {z' : Fin m'},
      Injective ρ' →
      (∀ i, Γ'' (ρ' i) = ((Fin.cons ⟨0, Q, τ₁⟩ Γ : Fin (n + 1) → Scheme P k) i).ds) →
      (∀ i, ρ' i ≠ z') → Γ'' z' = CScheme.mono (.ev Q₂) →
      CHasType D sig Γ'' (push ρ' (Fin.cons (Usage.ofMult π) u₂) + single z') (t₂ ρ' z') τ.ds)
    {m : Nat} {Γ' : Fin m → CScheme P k} {ρ : Fin n → Fin m} {z : Fin m} (hρ : Injective ρ)
    (hΓ : ∀ i, Γ' (ρ i) = (Γ i).ds) (hev : Γ' z = CScheme.mono (.ev (π • Q₁ + Q₂))) :
    CHasType D sig Γ' (push ρ (π • u₁ + u₂) + single z) (dsLet π Q Q₁ Q₂ ρ z t₁ t₂) τ.ds := by
  have hρ2 := shift_injective (shift_injective hρ)
  have hρ3 := shift_injective hρ2
  have hρ4 := shift_injective hρ3
  have hρ5 := shift_injective hρ4
  cases π with
  | one =>
    simp only [dsLet]
    have hb : CHasType D sig (Fin.cons (CScheme.mono (CTy.ev ((Mult.one : Mult) • Q₁))) (Fin.cons (CScheme.mono (CTy.ev Q₂)) Γ'))
        (single 0 + push (shift (shift ρ)) u₁)
        (if Q = 0 then .let_ .one (.prim (.coe Q₁ (Q₁ + Q)) (.var 0)) (t₁ (shift (shift (shift ρ))) 0)
           else .lam (.let_ .one (.prim (.join Q₁ Q) (.pair (.var (Fin.succ 0)) (.var 0)))
                  (t₁ (shift (shift (shift (shift ρ)))) 0)))
        (Scheme.ds ⟨0, Q, τ₁⟩).τ := by
      by_cases hQ : Q = 0
      · subst hQ
        rw [if_pos rfl]
        have h := ht₁ (Γ'' := Fin.cons (CScheme.mono (CTy.ev (Q₁ + 0))) (Fin.cons (CScheme.mono (CTy.ev ((Mult.one : Mult) • Q₁)))
            (Fin.cons (CScheme.mono (CTy.ev Q₂)) Γ'))) (ρ' := shift (shift (shift ρ))) (z' := 0) hρ3
          (by intro i; simp [hΓ]) (by intro i; simp) rfl
        refine (CHasType.let_ (π := .one) (.prim (.coe ?_) (var_ev (z := 0) rfl)) (h.cast
          (u' := Fin.cons (Usage.ofMult .one) (push (shift (shift ρ)) u₁)) ?_ rfl)).cast ?_ ?_
        · simpa using (hD.lawful k).refl Q₁
        · simp [push_shift, hρ2, single_zero_eq, cons_add_cons]
        · simp
        · simp [Scheme.ds]
      · rw [if_neg hQ]
        have h := ht₁ (Γ'' := Fin.cons (CScheme.mono (CTy.ev (Q₁ + Q))) (Fin.cons (CScheme.mono (CTy.ev Q))
            (Fin.cons (CScheme.mono (CTy.ev ((Mult.one : Mult) • Q₁))) (Fin.cons (CScheme.mono (CTy.ev Q₂)) Γ'))))
          (ρ' := shift (shift (shift (shift ρ)))) (z' := 0) hρ4
          (by intro i; simp [hΓ]) (by intro i; simp) rfl
        have hj := CHasType.prim (.join Q₁ Q) (CHasType.pair
          (var_ev (D := D) (sig := sig) (Γ' := Fin.cons (CScheme.mono (CTy.ev Q))
            (Fin.cons (CScheme.mono (CTy.ev ((Mult.one : Mult) • Q₁))) (Fin.cons (CScheme.mono (CTy.ev Q₂)) Γ')))
            (z := Fin.succ 0) (Q := Q₁) (by simp))
          (var_ev (z := 0) rfl))
        refine (CHasType.lam ((CHasType.let_ (π := .one) hj (h.cast
          (u' := Fin.cons (Usage.ofMult .one) (push (shift (shift (shift ρ))) u₁)) ?_ rfl)).cast
          (u' := Fin.cons (Usage.ofMult .one) (single 0 + push (shift (shift ρ)) u₁)) ?_ rfl)).cast
          rfl ?_
        · simp [push_shift, hρ3, single_zero_eq, cons_add_cons]
        · simp [push_shift, hρ2, single_zero_eq, single_one_eq, cons_add_cons]
        · simp [Scheme.ds, hQ]
    have h₂ := ht₂ (Γ'' := Fin.cons (Scheme.ds ⟨0, Q, τ₁⟩)
        (Fin.cons (CScheme.mono (CTy.ev ((Mult.one : Mult) • Q₁))) (Fin.cons (CScheme.mono (CTy.ev Q₂)) Γ')))
      (ρ' := liftR (shift (shift ρ))) (z' := Fin.succ (Fin.succ 0)) (liftR_injective hρ2)
      (by intro i; cases i using Fin.cases <;> simp [hΓ])
      (by intro i; cases i using Fin.cases <;> simp only [liftR_zero, liftR_succ, shift_apply,
          ne_eq, Fin.ext_iff, Fin.val_succ, Fin.val_zero] <;> omega) rfl
    refine (CHasType.letPair (.prim (.split _ _) (var_ev hev)) ((CHasType.let_ (π := .one) hb
      (h₂.cast (u' := Fin.cons (Usage.ofMult .one) (push (shift (shift ρ)) u₂ + single 1))
        ?_ rfl)).cast
      (u' := Fin.cons Usage.one (Fin.cons Usage.one (push ρ ((Mult.one : Mult) • u₁ + u₂))))
        ?_ rfl)).cast ?_ rfl
    · simp [push_liftR, hρ2, single_one_eq, single_two_eq, cons_add_cons]
    · simp [push_add, push_shift, shift_injective, hρ, single_zero_eq,
        single_one_eq, cons_add_cons]
    · abel
  | omega =>
    simp only [dsLet]
    have hb : CHasType D sig (Fin.cons (CScheme.mono (CTy.ev ((Mult.omega : Mult) • Q₁)))
          (Fin.cons (CScheme.mono (CTy.ev ((Mult.omega : Mult) • Q₁))) (Fin.cons (CScheme.mono (CTy.ev Q₂)) Γ')))
        (single 0 + push (shift (shift (shift ρ))) u₁)
        (if Q = 0 then
              .let_ .one (.prim (.coe ((Mult.omega : Mult) • Q₁) (Q₁ + Q)) (.var 0))
                (t₁ (shift (shift (shift (shift ρ)))) 0)
             else .lam (.let_ .one (.prim (.join Q₁ Q)
                    (.pair (.prim (.coe ((Mult.omega : Mult) • Q₁) Q₁) (.var (Fin.succ 0)))
                      (.var 0)))
                  (t₁ (shift (shift (shift (shift (shift ρ))))) 0)))
        (Scheme.ds ⟨0, Q, τ₁⟩).τ := by
      by_cases hQ : Q = 0
      · subst hQ
        rw [if_pos rfl]
        have h := ht₁ (Γ'' := Fin.cons (CScheme.mono (CTy.ev (Q₁ + 0))) (Fin.cons (CScheme.mono (CTy.ev ((Mult.omega : Mult) • Q₁)))
            (Fin.cons (CScheme.mono (CTy.ev ((Mult.omega : Mult) • Q₁))) (Fin.cons (CScheme.mono (CTy.ev Q₂)) Γ'))))
          (ρ' := shift (shift (shift (shift ρ)))) (z' := 0) hρ4
          (by intro i; simp [hΓ]) (by intro i; simp) rfl
        refine (CHasType.let_ (π := .one) (.prim (.coe ?_) (var_ev (z := 0) rfl)) (h.cast
          (u' := Fin.cons (Usage.ofMult .one) (push (shift (shift (shift ρ))) u₁)) ?_ rfl)).cast
          ?_ ?_
        · simpa using (hD.lawful k).omega_smul_entails Q₁
        · simp [push_shift, hρ3, single_zero_eq, cons_add_cons]
        · simp
        · simp [Scheme.ds]
      · rw [if_neg hQ]
        have h := ht₁ (Γ'' := Fin.cons (CScheme.mono (CTy.ev (Q₁ + Q))) (Fin.cons (CScheme.mono (CTy.ev Q))
            (Fin.cons (CScheme.mono (CTy.ev ((Mult.omega : Mult) • Q₁)))
            (Fin.cons (CScheme.mono (CTy.ev ((Mult.omega : Mult) • Q₁))) (Fin.cons (CScheme.mono (CTy.ev Q₂)) Γ')))))
          (ρ' := shift (shift (shift (shift (shift ρ))))) (z' := 0) hρ5
          (by intro i; simp [hΓ]) (by intro i; simp) rfl
        have hj := CHasType.prim (.join Q₁ Q) (CHasType.pair
          (CHasType.prim (.coe ((hD.lawful k).omega_smul_entails Q₁))
            (var_ev (D := D) (sig := sig) (Γ' := Fin.cons (CScheme.mono (CTy.ev Q))
              (Fin.cons (CScheme.mono (CTy.ev ((Mult.omega : Mult) • Q₁)))
              (Fin.cons (CScheme.mono (CTy.ev ((Mult.omega : Mult) • Q₁))) (Fin.cons (CScheme.mono (CTy.ev Q₂)) Γ'))))
              (z := Fin.succ 0) rfl))
          (var_ev (z := 0) rfl))
        refine (CHasType.lam ((CHasType.let_ (π := .one) hj (h.cast
          (u' := Fin.cons (Usage.ofMult .one) (push (shift (shift (shift (shift ρ)))) u₁))
            ?_ rfl)).cast
          (u' := Fin.cons (Usage.ofMult .one) (single 0 + push (shift (shift (shift ρ))) u₁))
            ?_ rfl)).cast rfl ?_
        · simp [push_shift, hρ4, single_zero_eq, cons_add_cons]
        · simp [push_shift, hρ3, single_zero_eq, single_one_eq, cons_add_cons]
        · simp [Scheme.ds, hQ]
    have h₂ := ht₂ (Γ'' := Fin.cons (Scheme.ds ⟨0, Q, τ₁⟩) (Fin.cons (CScheme.mono (CTy.ev ((Mult.omega : Mult) • Q₁)))
          (Fin.cons (CScheme.mono (CTy.ev ((Mult.omega : Mult) • Q₁))) (Fin.cons (CScheme.mono (CTy.ev Q₂)) Γ'))))
      (ρ' := liftR (shift (shift (shift ρ)))) (z' := Fin.succ (Fin.succ (Fin.succ 0)))
      (liftR_injective hρ3)
      (by intro i; cases i using Fin.cases <;> simp [hΓ])
      (by intro i; cases i using Fin.cases <;> simp only [liftR_zero, liftR_succ, shift_apply,
          ne_eq, Fin.ext_iff, Fin.val_succ, Fin.val_zero] <;> omega) rfl
    have hl := CHasType.let_ (π := .omega) hb (h₂.cast
      (u' := Fin.cons (Usage.ofMult .omega) (push (shift (shift (shift ρ))) u₂ + single 2))
        (by simp [push_liftR, hρ3, single_succ_eq, single_one_eq, single_two_eq, cons_add_cons])
        rfl)
    have hu := CHasType.prim (u := single 0) (.urEv Q₁)
      (var_ev (D := D) (sig := sig) (Γ' := Fin.cons (CScheme.mono (CTy.ev ((Mult.omega : Mult) • Q₁)))
          (Fin.cons (CScheme.mono (CTy.ev Q₂)) Γ')) (z := 0) rfl)
    refine (CHasType.letPair (.prim (.split _ _) (var_ev hev)) ((CHasType.letUr hu
      (hl.cast (u' := Fin.cons Usage.omega ((Mult.omega : Mult) • push (shift (shift ρ)) u₁ +
          push (shift (shift ρ)) u₂ + single 1)) ?_ rfl)).cast
      (u' := Fin.cons Usage.one (Fin.cons Usage.one (push ρ ((Mult.omega : Mult) • u₁ + u₂))))
        ?_ rfl)).cast ?_ rfl
    · simp [push_shift, hρ2, single_zero_eq, single_one_eq, single_two_eq,
        cons_add_cons, smul_cons]
      abel
    · simp [push_add, push_smul, push_shift, shift_injective, hρ, single_zero_eq,
        single_one_eq, cons_add_cons, smul_cons]
    · abel


lemma cctxWk_ev {k n : Nat} (j : Nat) {Γ : Fin n → CScheme P k} {x : Fin n}
    {X : SConstr (Atom P k)} (h : Γ x = CScheme.mono (.ev X)) :
    cctxWk j Γ x = CScheme.mono (.ev (X.wk j)) := by
  simp [cctxWk, h, CTy.rename, SConstr.wk_eq_rename]

lemma cctxWk_ds {k n m : Nat} (j : Nat) {Γ : Fin n → Scheme P k} {Γ' : Fin m → CScheme P k}
    {ρ : Fin n → Fin m} (hΓ : ∀ i, Γ' (ρ i) = (Γ i).ds) (i : Fin n) :
    cctxWk j Γ' (ρ i) = (ctxWk j Γ i).ds := by
  simp [cctxWk, ctxWk, hΓ, Scheme.ds_rename]

/-- Typing of the translation of `let`-bindings with a signature. -/
theorem dsLetSig_typed {D : LDomain (Atom P)} (hD : D.Lawful) {sig : DataSig P} {k n : Nat}
    {π : Mult} {Q₁ Q₂ : SConstr (Atom P k)} {Γ : Fin n → Scheme P k} {u₁ u₂ : Fin n → Usage}
    {σ : Scheme P k} {τ : Ty P k}
    {t₁ : ∀ {m' : Nat}, (Fin n → Fin m') → Fin m' → CTm sig (k + σ.j) m'}
    {t₂ : ∀ {m' : Nat}, (Fin (n + 1) → Fin m') → Fin m' → CTm sig k m'}
    (ht₁ : ∀ {m' : Nat} {Γ'' : Fin m' → CScheme P (k + σ.j)} {ρ' : Fin n → Fin m'}
      {z' : Fin m'}, Injective ρ' → (∀ i, Γ'' (ρ' i) = (ctxWk σ.j Γ i).ds) →
      (∀ i, ρ' i ≠ z') → Γ'' z' = CScheme.mono (.ev (Q₁.wk σ.j + σ.Q)) →
      CHasType D sig Γ'' (push ρ' u₁ + single z') (t₁ ρ' z') σ.τ.ds)
    (ht₂ : ∀ {m' : Nat} {Γ'' : Fin m' → CScheme P k} {ρ' : Fin (n + 1) → Fin m'} {z' : Fin m'},
      Injective ρ' →
      (∀ i, Γ'' (ρ' i) = ((Fin.cons σ Γ : Fin (n + 1) → Scheme P k) i).ds) →
      (∀ i, ρ' i ≠ z') → Γ'' z' = CScheme.mono (.ev Q₂) →
      CHasType D sig Γ'' (push ρ' (Fin.cons (Usage.ofMult π) u₂) + single z') (t₂ ρ' z') τ.ds)
    {m : Nat} {Γ' : Fin m → CScheme P k} {ρ : Fin n → Fin m} {z : Fin m} (hρ : Injective ρ)
    (hΓ : ∀ i, Γ' (ρ i) = (Γ i).ds) (hev : Γ' z = CScheme.mono (.ev (π • Q₁ + Q₂))) :
    CHasType D sig Γ' (push ρ (π • u₁ + u₂) + single z)
      (dsLetSig π σ.j σ.Q Q₁ Q₂ ρ z t₁ t₂) τ.ds := by
  cases σ with
  | mk j Q τ₁ =>
  have hρ2 := shift_injective (shift_injective hρ)
  have hρ3 := shift_injective hρ2
  have hρ4 := shift_injective hρ3
  have hρ5 := shift_injective hρ4
  cases π with
  | one =>
    simp only [dsLetSig]
    have hb : CHasType D sig (cctxWk j (Fin.cons (CScheme.mono (CTy.ev ((Mult.one : Mult) • Q₁)))
          (Fin.cons (CScheme.mono (CTy.ev Q₂)) Γ')))
        (single 0 + push (shift (shift ρ)) u₁)
        (if Q = 0 then
            .let_ .one (.prim (.coe (Q₁.wk j) (Q₁.wk j + Q)) (.var 0))
              (t₁ (shift (shift (shift ρ))) 0)
         else .lam (.let_ .one (.prim (.join (Q₁.wk j) Q) (.pair (.var (Fin.succ 0)) (.var 0)))
                (t₁ (shift (shift (shift (shift ρ)))) 0)))
        (Scheme.ds ⟨j, Q, τ₁⟩).τ := by
      by_cases hQ : Q = 0
      · subst hQ
        rw [if_pos rfl]
        have h := ht₁ (Γ'' := Fin.cons (CScheme.mono (CTy.ev (Q₁.wk j + 0)))
            (cctxWk j (Fin.cons (CScheme.mono (CTy.ev ((Mult.one : Mult) • Q₁)))
              (Fin.cons (CScheme.mono (CTy.ev Q₂)) Γ'))))
          (ρ' := shift (shift (shift ρ))) (z' := 0) hρ3
          (by intro i; simpa using cctxWk_ds j hΓ i) (by intro i; simp) rfl
        refine (CHasType.let_ (π := .one) (.prim (.coe ?_) (var_ev (z := 0)
          (cctxWk_ev (Γ := Fin.cons (CScheme.mono (CTy.ev ((Mult.one : Mult) • Q₁)))
            (Fin.cons (CScheme.mono (CTy.ev Q₂)) Γ')) (x := 0) j rfl))) (h.cast
          (u' := Fin.cons (Usage.ofMult .one) (push (shift (shift ρ)) u₁)) ?_ rfl)).cast ?_ ?_
        · simpa using (hD.lawful _).refl (Q₁.wk j)
        · simp [push_shift, hρ2, single_zero_eq, cons_add_cons]
        · simp
        · simp [Scheme.ds]
      · rw [if_neg hQ]
        have h := ht₁ (Γ'' := Fin.cons (CScheme.mono (CTy.ev (Q₁.wk j + Q)))
            (Fin.cons (CScheme.mono (CTy.ev Q))
            (cctxWk j (Fin.cons (CScheme.mono (CTy.ev ((Mult.one : Mult) • Q₁)))
              (Fin.cons (CScheme.mono (CTy.ev Q₂)) Γ')))))
          (ρ' := shift (shift (shift (shift ρ)))) (z' := 0) hρ4
          (by intro i; simpa using cctxWk_ds j hΓ i) (by intro i; simp) rfl
        have hj := CHasType.prim (.join (Q₁.wk j) Q) (CHasType.pair
          (var_ev (D := D) (sig := sig) (Γ' := Fin.cons (CScheme.mono (CTy.ev Q))
            (cctxWk j (Fin.cons (CScheme.mono (CTy.ev ((Mult.one : Mult) • Q₁)))
              (Fin.cons (CScheme.mono (CTy.ev Q₂)) Γ'))))
            (z := Fin.succ 0) (Q := Q₁.wk j) (by simpa using cctxWk_ev (x := 0) j rfl))
          (var_ev (z := 0) rfl))
        refine (CHasType.lam ((CHasType.let_ (π := .one) hj (h.cast
          (u' := Fin.cons (Usage.ofMult .one) (push (shift (shift (shift ρ))) u₁)) ?_ rfl)).cast
          (u' := Fin.cons (Usage.ofMult .one) (single 0 + push (shift (shift ρ)) u₁)) ?_ rfl)).cast
          rfl ?_
        · simp [push_shift, hρ3, single_zero_eq, cons_add_cons]
        · simp [push_shift, hρ2, single_zero_eq, single_one_eq, cons_add_cons]
        · simp [Scheme.ds, hQ]
    have h₂ := ht₂ (Γ'' := Fin.cons (Scheme.ds ⟨j, Q, τ₁⟩)
        (Fin.cons (CScheme.mono (CTy.ev ((Mult.one : Mult) • Q₁)))
          (Fin.cons (CScheme.mono (CTy.ev Q₂)) Γ')))
      (ρ' := liftR (shift (shift ρ))) (z' := Fin.succ (Fin.succ 0)) (liftR_injective hρ2)
      (by intro i; cases i using Fin.cases <;> simp [hΓ])
      (by intro i; cases i using Fin.cases <;> simp only [liftR_zero, liftR_succ, shift_apply,
          ne_eq, Fin.ext_iff, Fin.val_succ, Fin.val_zero] <;> omega) rfl
    refine (CHasType.letPair (.prim (.split _ _) (var_ev hev)) ((CHasType.letGen (π := .one) hb
      (h₂.cast (u' := Fin.cons (Usage.ofMult .one) (push (shift (shift ρ)) u₂ + single 1))
        ?_ rfl)).cast
      (u' := Fin.cons Usage.one (Fin.cons Usage.one (push ρ ((Mult.one : Mult) • u₁ + u₂))))
        ?_ rfl)).cast ?_ rfl
    · simp [push_liftR, hρ2, single_one_eq, single_two_eq, cons_add_cons]
    · simp [push_add, push_shift, shift_injective, hρ, single_zero_eq,
        single_one_eq, cons_add_cons]
    · abel
  | omega =>
    simp only [dsLetSig]
    have hb : CHasType D sig (cctxWk j (Fin.cons (CScheme.mono (CTy.ev ((Mult.omega : Mult) • Q₁)))
          (Fin.cons (CScheme.mono (CTy.ev ((Mult.omega : Mult) • Q₁)))
            (Fin.cons (CScheme.mono (CTy.ev Q₂)) Γ'))))
        (single 0 + push (shift (shift (shift ρ))) u₁)
        (if Q = 0 then
              .let_ .one (.prim (.coe (((Mult.omega : Mult) • Q₁).wk j) (Q₁.wk j + Q)) (.var 0))
                (t₁ (shift (shift (shift (shift ρ)))) 0)
             else .lam (.let_ .one (.prim (.join (Q₁.wk j) Q)
                    (.pair (.prim (.coe (((Mult.omega : Mult) • Q₁).wk j) (Q₁.wk j))
                      (.var (Fin.succ 0))) (.var 0)))
                  (t₁ (shift (shift (shift (shift (shift ρ))))) 0)))
        (Scheme.ds ⟨j, Q, τ₁⟩).τ := by
      by_cases hQ : Q = 0
      · subst hQ
        rw [if_pos rfl]
        have h := ht₁ (Γ'' := Fin.cons (CScheme.mono (CTy.ev (Q₁.wk j + 0)))
            (cctxWk j (Fin.cons (CScheme.mono (CTy.ev ((Mult.omega : Mult) • Q₁)))
            (Fin.cons (CScheme.mono (CTy.ev ((Mult.omega : Mult) • Q₁)))
              (Fin.cons (CScheme.mono (CTy.ev Q₂)) Γ')))))
          (ρ' := shift (shift (shift (shift ρ)))) (z' := 0) hρ4
          (by intro i; simpa using cctxWk_ds j hΓ i) (by intro i; simp) rfl
        refine (CHasType.let_ (π := .one) (.prim (.coe ?_) (var_ev (z := 0)
          (cctxWk_ev (Γ := Fin.cons (CScheme.mono (CTy.ev ((Mult.omega : Mult) • Q₁)))
            (Fin.cons (CScheme.mono (CTy.ev ((Mult.omega : Mult) • Q₁)))
              (Fin.cons (CScheme.mono (CTy.ev Q₂)) Γ'))) (x := 0) j rfl))) (h.cast
          (u' := Fin.cons (Usage.ofMult .one) (push (shift (shift (shift ρ))) u₁)) ?_ rfl)).cast
          ?_ ?_
        · simpa using (hD.lawful _).omega_smul_entails (Q₁.wk j)
        · simp [push_shift, hρ3, single_zero_eq, cons_add_cons]
        · simp
        · simp [Scheme.ds]
      · rw [if_neg hQ]
        have h := ht₁ (Γ'' := Fin.cons (CScheme.mono (CTy.ev (Q₁.wk j + Q)))
            (Fin.cons (CScheme.mono (CTy.ev Q))
            (cctxWk j (Fin.cons (CScheme.mono (CTy.ev ((Mult.omega : Mult) • Q₁)))
            (Fin.cons (CScheme.mono (CTy.ev ((Mult.omega : Mult) • Q₁)))
              (Fin.cons (CScheme.mono (CTy.ev Q₂)) Γ'))))))
          (ρ' := shift (shift (shift (shift (shift ρ))))) (z' := 0) hρ5
          (by intro i; simpa using cctxWk_ds j hΓ i) (by intro i; simp) rfl
        have hj := CHasType.prim (.join (Q₁.wk j) Q) (CHasType.pair
          (CHasType.prim (.coe (by simpa using (hD.lawful _).omega_smul_entails (Q₁.wk j)))
            (var_ev (D := D) (sig := sig) (Γ' := Fin.cons (CScheme.mono (CTy.ev Q))
              (cctxWk j (Fin.cons (CScheme.mono (CTy.ev ((Mult.omega : Mult) • Q₁)))
              (Fin.cons (CScheme.mono (CTy.ev ((Mult.omega : Mult) • Q₁)))
                (Fin.cons (CScheme.mono (CTy.ev Q₂)) Γ')))))
              (z := Fin.succ 0) (Q := ((Mult.omega : Mult) • Q₁).wk j)
              (by rw [Fin.cons_succ]; exact cctxWk_ev (x := 0) j rfl)))
          (var_ev (z := 0) rfl))
        refine (CHasType.lam ((CHasType.let_ (π := .one) hj (h.cast
          (u' := Fin.cons (Usage.ofMult .one) (push (shift (shift (shift (shift ρ)))) u₁))
            ?_ rfl)).cast
          (u' := Fin.cons (Usage.ofMult .one) (single 0 + push (shift (shift (shift ρ))) u₁))
            ?_ rfl)).cast rfl ?_
        · simp [push_shift, hρ4, single_zero_eq, cons_add_cons]
        · simp [push_shift, hρ3, single_zero_eq, single_one_eq, cons_add_cons]
        · simp [Scheme.ds, hQ]
    have h₂ := ht₂ (Γ'' := Fin.cons (Scheme.ds ⟨j, Q, τ₁⟩)
        (Fin.cons (CScheme.mono (CTy.ev ((Mult.omega : Mult) • Q₁)))
          (Fin.cons (CScheme.mono (CTy.ev ((Mult.omega : Mult) • Q₁)))
            (Fin.cons (CScheme.mono (CTy.ev Q₂)) Γ'))))
      (ρ' := liftR (shift (shift (shift ρ)))) (z' := Fin.succ (Fin.succ (Fin.succ 0)))
      (liftR_injective hρ3)
      (by intro i; cases i using Fin.cases <;> simp [hΓ])
      (by intro i; cases i using Fin.cases <;> simp only [liftR_zero, liftR_succ, shift_apply,
          ne_eq, Fin.ext_iff, Fin.val_succ, Fin.val_zero] <;> omega) rfl
    have hl := CHasType.letGen (π := .omega) hb (h₂.cast
      (u' := Fin.cons (Usage.ofMult .omega) (push (shift (shift (shift ρ))) u₂ + single 2))
        (by simp [push_liftR, hρ3, single_succ_eq, single_one_eq, single_two_eq, cons_add_cons])
        rfl)
    have hu := CHasType.prim (u := single 0) (.urEv Q₁)
      (var_ev (D := D) (sig := sig) (Γ' := Fin.cons (CScheme.mono (CTy.ev ((Mult.omega : Mult) • Q₁)))
          (Fin.cons (CScheme.mono (CTy.ev Q₂)) Γ')) (z := 0) rfl)
    refine (CHasType.letPair (.prim (.split _ _) (var_ev hev)) ((CHasType.letUr hu
      (hl.cast (u' := Fin.cons Usage.omega ((Mult.omega : Mult) • push (shift (shift ρ)) u₁ +
          push (shift (shift ρ)) u₂ + single 1)) ?_ rfl)).cast
      (u' := Fin.cons Usage.one (Fin.cons Usage.one (push ρ ((Mult.omega : Mult) • u₁ + u₂))))
        ?_ rfl)).cast ?_ rfl
    · simp [push_shift, hρ2, single_zero_eq, single_one_eq, single_two_eq,
        cons_add_cons, smul_cons]
      abel
    · simp [push_add, push_smul, push_shift, shift_injective, hρ, single_zero_eq,
        single_one_eq, cons_add_cons, smul_cons]
    · abel

-- [NOT IN PAPER ◀ END] auxiliary lemmas for Theorem 7.1

end LQT
