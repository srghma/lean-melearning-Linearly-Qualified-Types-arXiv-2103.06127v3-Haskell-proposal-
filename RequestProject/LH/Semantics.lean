module

public import RequestProject.LH.Subst

/-!
# Operational semantics, type preservation and progress for `λq→` (cf. §3.4)

The paper (§3.4 "Metatheory") states type preservation (Theorem 3.5) and progress
(Theorem 3.6) for a Launchbury-style big-step semantics with linear environments, given in its
Appendix A.  That appendix is **not part of the supplied text**, so we cannot formalize the
paper's own semantics.  Instead we give the standard substitution-based *call-by-name*
(lazy, weak-head) small-step semantics, and prove the corresponding theorems for it:

* `Step` : `(λ_π (x:A). t) s ⟶ t[s/x]`, `(λp. t) π ⟶ t[π/p]`,
  `case_π (c_k t⃗) of {…} ⟶ u_k[t⃗/x⃗]`, `let_π x⃗ = t⃗ in u ⟶ u[t⃗/x⃗]`, and reduction in
  the head position of applications and in the scrutinee of `case`;
* `HasType.preservation` : reduction preserves the type **and the multiplicities** of every
  variable of the context;
* `HasType.progress` : a well-typed term without free term variables is a value or reduces;
* `HasType.type_safety` : such a term never reaches a stuck term.

Preservation with the *same* usage vector is the substitution-semantics analogue of the paper's
linearity guarantee: reducing never changes how many times each free variable is consumed.
-/

@[expose] public section

namespace LH

variable {S : Sig}

-- [NOT IN PAPER ▶ START] call-by-name small-step semantics (the paper's semantics is in its
--   Appendix A, which is not part of the supplied text)
/-- Values (weak head normal forms) of the call-by-name semantics. -/
inductive Value : {m n : Nat} → Tm S m n → Prop
  | lam {m n} (π : Mult m) (A : S.Ty m) (t : Tm S m (n + 1)) : Value (.lam π A t)
  | mlam {m n} (t : Tm S (m + 1) n) : Value (.mlam t)
  | con {m n} (d : S.Dn) (k : Fin (S.ncons d)) (args : Fin (S.arity d k) → Tm S m n) :
      Value (.con d k args)

/-- One step of call-by-name reduction. -/
inductive Step : {m n : Nat} → Tm S m n → Tm S m n → Prop
  | beta {m n} (π : Mult m) (A : S.Ty m) (t : Tm S m (n + 1)) (s : Tm S m n) :
      Step (.app (.lam π A t) s) (t.subst (Fin.cons s Tm.var))
  | mbeta {m n} (t : Tm S (m + 1) n) (π : Mult m) :
      Step (.mapp (.mlam t) π) (t.msubst (Fin.cons π Mult.var))
  | caseCon {m n} (π : Mult m) (d : S.Dn) (k : Fin (S.ncons d))
      (args : Fin (S.arity d k) → Tm S m n) (brs : (k : Fin (S.ncons d)) → Tm S m (n + S.arity d k)) :
      Step (.case π (.con d k args) d brs) ((brs k).subst (Fin.append Tm.var args))
  | letSub {m n} (π : Mult m) (j : Nat) (tys : Fin j → S.Ty m) (rhs : Fin j → Tm S m n)
      (body : Tm S m (n + j)) :
      Step (.lett π j tys rhs body) (body.subst (Fin.append Tm.var rhs))
  | app_l {m n} {t t' : Tm S m n} (s : Tm S m n) : Step t t' → Step (.app t s) (.app t' s)
  | mapp_l {m n} {t t' : Tm S m n} (π : Mult m) : Step t t' → Step (.mapp t π) (.mapp t' π)
  | case_scrut {m n} {t t' : Tm S m n} (π : Mult m) (d : S.Dn)
      (brs : (k : Fin (S.ncons d)) → Tm S m (n + S.arity d k)) :
      Step t t' → Step (.case π t d brs) (.case π t' d brs)

/-- Typing of the substitution `x⃗ ↦ t⃗` that keeps the other variables. -/
theorem hasType_append_subst {m n j : Nat} {Γ : Fin n → S.Ty m} (f : Fin j → S.Ty m)
    (args : Fin j → Tm S m n) (w : Fin j → Fin n → Usage m)
    (hargs : ∀ i, HasType S Γ (w i) (args i) (f i)) :
    ∀ x, HasType S Γ (Fin.append (fun y => Pi.single y 1) w x) (Fin.append Tm.var args x)
      (Fin.append Γ f x) := by
  intro x
  refine Fin.addCases (fun y => ?_) (fun y => ?_) x
  · simp only [Fin.append_left]
    exact .var y 0 (by simp)
  · simp only [Fin.append_right]
    exact hargs y

theorem mix_append_single {m n j : Nat} (w : Fin j → Fin n → Usage m) (u : Fin n → Usage m)
    (f : Fin j → Usage m) :
    mix (Fin.append (fun y => Pi.single y 1) w) (Fin.append u f) = u + ∑ i, f i • w i := by
  unfold mix
  rw [Fin.sum_univ_add]
  simp only [Fin.append_left, Fin.append_right]
  congr 1
  exact mix_single_self u

/-- **Type preservation**: reduction preserves the type and the multiplicities. -/
theorem HasType.preservation {m n : Nat} {Γ : Fin n → S.Ty m} {u : Fin n → Usage m}
    {t t' : Tm S m n} {A : S.Ty m} (h : HasType S Γ u t A) (hs : Step t t') :
    HasType S Γ u t' A := by
  induction hs generalizing u A with
  | beta π A' t s =>
    cases h with
    | app h₁ h₂ hu =>
      cases h₁ with
      | lam hb =>
        rw [hu]
        exact hb.subst_one h₂
  | mbeta t π =>
    cases h with
    | mapp h₁ =>
      cases h₁ with
      | mlam hb =>
        have := hb.msubst (Fin.cons π Mult.var)
        have e₁ : (fun x => ((Γ x).wk).subst (Fin.cons π Mult.var)) = Γ := by
          funext x; exact Ty.subst_cons_wk π (Γ x)
        have e₂ : substU (Fin.cons π Mult.var) (fun x => Usage.wk (u x)) = u := by
          funext x; exact Usage.subst_cons_wk π (u x)
        rw [e₁, e₂] at this
        exact this
  | caseCon π d k args brs =>
    cases h with
    | @case _ _ _ _ u₁ u₂ _ _ _ ps _ _ h₁ hbrs hu =>
      cases h₁ with
      | con v w hargs hu₁ =>
        have := (hbrs k).subst _ Γ _ (hasType_append_subst _ args w hargs)
        rw [mix_append_single] at this
        have := this.weaken_omega (Usage.nz π • v)
        convert this using 1
        rw [hu, hu₁, smul_add, Finset.smul_sum]
        simp only [smul_smul, ← Usage.nz_mul_nz]
        rw [mul_comm (Usage.nz π) Usage.omega]
        abel
  | letSub π j tys rhs body =>
    cases h with
    | @lett _ _ _ _ u₂ _ _ _ _ _ _ w hrhs hbody hu =>
      have := hbody.subst _ Γ _ (hasType_append_subst tys rhs w hrhs)
      rw [mix_append_single, ← Finset.smul_sum] at this
      rw [hu]
      exact this
  | app_l s _ ih =>
    cases h with
    | app h₁ h₂ hu => exact .app (ih h₁) h₂ hu
  | mapp_l π _ ih =>
    cases h with
    | mapp h₁ => exact .mapp (ih h₁)
  | case_scrut π d brs _ ih =>
    cases h with
    | case h₁ hbrs hu => exact .case (ih h₁) hbrs hu

theorem HasType.progress_aux {m n : Nat} {Γ : Fin n → S.Ty m} {u : Fin n → Usage m}
    {t : Tm S m n} {A : S.Ty m} (h : HasType S Γ u t A) :
    n = 0 → Value t ∨ ∃ t', Step t t' := by
  induction h with
  | var x => intro hn; subst hn; exact x.elim0
  | lam => exact fun _ => .inl (.lam _ _ _)
  | mlam => exact fun _ => .inl (.mlam _)
  | con => exact fun _ => .inl (.con _ _ _)
  | @app m n Γ u u₁ u₂ t s π A B h₁ _ _ ih₁ _ =>
    intro hn
    rcases ih₁ hn with hv | ⟨t', ht'⟩
    · cases hv with
      | lam π' A' b => exact .inr ⟨_, .beta π' A' b s⟩
      | mlam => cases h₁
      | con => cases h₁
    · exact .inr ⟨_, .app_l s ht'⟩
  | @mapp m n Γ u t A π h₁ ih₁ =>
    intro hn
    rcases ih₁ hn with hv | ⟨t', ht'⟩
    · cases hv with
      | lam => cases h₁
      | mlam b => exact .inr ⟨_, .mbeta b π⟩
      | con => cases h₁
    · exact .inr ⟨_, .mapp_l π ht'⟩
  | @case m n Γ u u₁ u₂ π t d ps brs C h₁ _ _ ih₁ _ =>
    intro hn
    rcases ih₁ hn with hv | ⟨t', ht'⟩
    · cases hv with
      | lam => cases h₁
      | mlam => cases h₁
      | con d' k args =>
        cases h₁
        exact .inr ⟨_, .caseCon π d k args brs⟩
    · exact .inr ⟨_, .case_scrut π d brs ht'⟩
  | lett => exact fun _ => .inr ⟨_, .letSub _ _ _ _ _⟩

/-- **Progress**: a well-typed term without free term variables is a value or reduces. -/
theorem HasType.progress {m : Nat} {Γ : Fin 0 → S.Ty m} {u : Fin 0 → Usage m}
    {t : Tm S m 0} {A : S.Ty m} (h : HasType S Γ u t A) : Value t ∨ ∃ t', Step t t' :=
  h.progress_aux rfl

/-- **Type safety**: a well-typed term without free term variables never reduces to a stuck
term, and keeps its type along reduction. -/
theorem HasType.type_safety {m : Nat} {Γ : Fin 0 → S.Ty m} {u : Fin 0 → Usage m}
    {t t' : Tm S m 0} {A : S.Ty m} (h : HasType S Γ u t A)
    (hs : Relation.ReflTransGen Step t t') :
    HasType S Γ u t' A ∧ (Value t' ∨ ∃ t'', Step t' t'') := by
  have ht' : HasType S Γ u t' A := by
    induction hs with
    | refl => exact h
    | tail _ hst ih => exact ih.preservation hst
  exact ⟨ht', ht'.progress⟩
-- [NOT IN PAPER ◀ END]

end LH
