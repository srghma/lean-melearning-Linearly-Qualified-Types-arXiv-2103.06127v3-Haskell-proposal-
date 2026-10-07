module

public import RequestProject.LQT.Ch6_ConstraintInference.Generation

/-!
# Constraint generation with rule G_LetGen (ott source; not in Figure 8)

Paper location: the typing-rule source `ott.tex` defines one more constraint-generation rule,
**G_LetGen**, which is *not* displayed in Figure 8 of the paper (§6.2 says "we do not model
`let`-generalisation", and Figure 8 lists only Var, Abs, App, Pack, Unpack, Case, Let, LetSig).
For completeness we formalize it here as an extension:

```
Γ₁ ⊢ᵢ e₁ : τ₁ ⇝ C₁     Q_r ⊗ Q ⊢ C₁     Γ₂, x :_π Q ⊸ τ₁ ⊢ᵢ e₂ : τ ⇝ C₂
───────────────────────────────────────────────────────────────────────── G_LetGen
        π·Γ₁ + Γ₂ ⊢ᵢ let_π x = e₁ in e₂ : τ ⇝ π·Q_r ⊗ C₂
```

The rule generalises the (monomorphic) type of an unannotated `let` over a constraint `Q`: the
residual `Q_r` is what `e₁` needs besides `Q`.  Since its premise `Q_r ⊗ Q ⊢ C₁` mentions the
entailment relation, the extended judgement `GenG D sig` is parametrised by the domain `D`.
It contains every rule of Figure 8 (`Gen.toGenG`) plus G_LetGen.

We prove that the extension is still sound (`LDomain.Lawful.genG_sound`, the analogue of
Lemma 6.4): the conclusion of G_LetGen is justified by rule E_Let of Figure 6, which binds `x`
to the qualified type `Q ⊸ τ₁`.
-/

@[expose] public section

namespace LQT

open SConstr

variable {P : Type}

-- [NOT IN PAPER ▶ START] rule G_LetGen of the ott source (not displayed in Figure 8): the
--   judgement `Γ ⊢ᵢ e : τ ⇝ C` extended with G_LetGen
/-- Constraint generation (Figure 8) extended with rule G_LetGen of the ott source. -/
inductive GenG (D : LDomain (Atom P)) (sig : DataSig P) :
    {k n : Nat} → (Fin n → Scheme P k) → (Fin n → Usage) → Tm sig k n → Ty P k →
      Wanted (Atom P) k → Prop
  /-- G_Var -/
  | var {k n} {Γ : Fin n → Scheme P k} {x : Fin n} {σ : Scheme P k} (v : Fin n → Usage)
      (τs : Fin σ.j → Ty P k) : Γ x = σ →
      GenG D sig Γ (single x + (Mult.omega : Mult) • v) (.var x) (σ.τ.subst (instSub τs))
        (.simple (σ.Q.tsubst (instSub τs)))
  /-- Data constructors. -/
  | con {k n} {Γ : Fin n → Scheme P k} (v : Fin n → Usage) (T : Nat) (i : Fin (sig.ncons T))
      (τs : Fin (sig.params T) → Ty P k) :
      GenG D sig Γ ((Mult.omega : Mult) • v) (.con T i) ((sig.conTy T i).subst τs) (.simple 0)
  /-- G_Abs -/
  | lam {k n} {Γ : Fin n → Scheme P k} {u : Fin n → Usage} {π : Mult} {τ₀ τ : Ty P k}
      {e : Tm sig k (n + 1)} {C : Wanted (Atom P) k} :
      GenG D sig (Fin.cons (Scheme.mono τ₀) Γ) (Fin.cons (Usage.ofMult π) u) e τ C →
      GenG D sig Γ u (.lam e) (.arr π τ₀ τ) C
  /-- G_App -/
  | app {k n} {Γ : Fin n → Scheme P k} {u₁ u₂ : Fin n → Usage} {π : Mult} {τ₂ τ : Ty P k}
      {e₁ e₂ : Tm sig k n} {C₁ C₂ : Wanted (Atom P) k} :
      GenG D sig Γ u₁ e₁ (.arr π τ₂ τ) C₁ → GenG D sig Γ u₂ e₂ τ₂ C₂ →
      GenG D sig Γ (u₁ + π • u₂) (.app e₁ e₂) τ (.tensor C₁ (π • C₂))
  /-- G_Case -/
  | case {k n} {Γ : Fin n → Scheme P k} {u₁ u₂ : Fin n → Usage} {π : Mult} {τ : Ty P k}
      {e : Tm sig k n} {T : Nat} {τs : Fin (sig.params T) → Ty P k}
      {alts : (i : Fin (sig.ncons T)) → Tm sig k (sig.arity T i + n)}
      {C : Wanted (Atom P) k} {Cs : Fin (sig.ncons T) → Wanted (Atom P) k} :
      GenG D sig Γ u₁ e (.data T (sig.params T) τs) C →
      (∀ i, GenG D sig (caseCtx sig Γ T i τs) (caseUsage sig π u₂ T i) (alts i) τ (Cs i)) →
      GenG D sig Γ (π • u₁ + u₂) (.case π e T alts) τ (.tensor (π • C) (withAll _ Cs))
  /-- G_Unpack -/
  | unpack {k n j m} {Γ : Fin n → Scheme P k} {u₁ u₂ : Fin n → Usage} {τ₁ : Ty P (k + j)}
      {mul : Fin m → Mult} {pred : Fin m → P} {ar : Fin m → Nat}
      {args : (i : Fin m) → Fin (ar i) → Ty P (k + j)} {τ : Ty P k}
      {e₁ : Tm sig k n} {e₂ : Tm sig (k + j) (n + 1)} {C₁ : Wanted (Atom P) k}
      {C₂ : Wanted (Atom P) (k + j)} :
      GenG D sig Γ u₁ e₁ (.exq j τ₁ m mul pred ar args) C₁ →
      GenG D sig (Fin.cons (Scheme.mono τ₁) (ctxWk j Γ)) (Fin.cons Usage.one u₂) e₂ (τ.wk j)
        C₂ →
      GenG D sig Γ (u₁ + u₂) (.unpack j e₁ e₂) τ
        (.tensor C₁ (.impl .one j (exqC m mul pred ar args) C₂))
  /-- G_Pack -/
  | pack {k n j m} {Γ : Fin n → Scheme P k} {u : Fin n → Usage} {τ : Ty P (k + j)}
      {mul : Fin m → Mult} {pred : Fin m → P} {ar : Fin m → Nat}
      {args : (i : Fin m) → Fin (ar i) → Ty P (k + j)} {e : Tm sig k n}
      {C : Wanted (Atom P) k} (υs : Fin j → Ty P k) :
      GenG D sig Γ u e (τ.subst (instSub υs)) C →
      GenG D sig Γ u (.pack e) (.exq j τ m mul pred ar args)
        (.tensor C (.simple ((exqC m mul pred ar args).tsubst (instSub υs))))
  /-- G_Let -/
  | let_ {k n} {Γ : Fin n → Scheme P k} {u₁ u₂ : Fin n → Usage} {π : Mult} {τ₁ τ : Ty P k}
      {e₁ : Tm sig k n} {e₂ : Tm sig k (n + 1)} {C₁ C₂ : Wanted (Atom P) k} :
      GenG D sig Γ u₁ e₁ τ₁ C₁ →
      GenG D sig (Fin.cons (Scheme.mono τ₁) Γ) (Fin.cons (Usage.ofMult π) u₂) e₂ τ C₂ →
      GenG D sig Γ (π • u₁ + u₂) (.let_ π e₁ e₂) τ (.tensor (π • C₁) C₂)
  /-- G_LetGen (ott source only): `let`-generalisation over a constraint `Q`, with residual
  constraint `Q_r`. -/
  | letGen {k n} {Γ : Fin n → Scheme P k} {u₁ u₂ : Fin n → Usage} {π : Mult} {τ₁ τ : Ty P k}
      {e₁ : Tm sig k n} {e₂ : Tm sig k (n + 1)} {C₁ C₂ : Wanted (Atom P) k}
      (Qr Q : SConstr (Atom P k)) :
      GenG D sig Γ u₁ e₁ τ₁ C₁ →
      D.WEntails (Qr + Q) C₁ →
      GenG D sig (Fin.cons ⟨0, Q, τ₁⟩ Γ) (Fin.cons (Usage.ofMult π) u₂) e₂ τ C₂ →
      GenG D sig Γ (π • u₁ + u₂) (.let_ π e₁ e₂) τ (.tensor (.simple (π • Qr)) C₂)
  /-- G_LetSig -/
  | letSig {k n} {Γ : Fin n → Scheme P k} {u₁ u₂ : Fin n → Usage} {π : Mult} {σ : Scheme P k}
      {τ : Ty P k} {e₁ : Tm sig (k + σ.j) n} {e₂ : Tm sig k (n + 1)}
      {C₁ : Wanted (Atom P) (k + σ.j)} {C₂ : Wanted (Atom P) k} :
      GenG D sig (ctxWk σ.j Γ) u₁ e₁ σ.τ C₁ →
      GenG D sig (Fin.cons σ Γ) (Fin.cons (Usage.ofMult π) u₂) e₂ τ C₂ →
      GenG D sig Γ (π • u₁ + u₂) (.letSig π σ e₁ e₂) τ (.tensor C₂ (.impl π σ.j σ.Q C₁))

/-- Every derivation of Figure 8 is a derivation of the extended system. -/
theorem Gen.toGenG {D : LDomain (Atom P)} {sig : DataSig P} {k n : Nat}
    {Γ : Fin n → Scheme P k} {u : Fin n → Usage} {e : Tm sig k n} {τ : Ty P k}
    {C : Wanted (Atom P) k} (h : Gen sig Γ u e τ C) : GenG D sig Γ u e τ C := by
  induction h with
  | var v τs hx => exact .var v τs hx
  | con v T i τs => exact .con v T i τs
  | lam _ ih => exact .lam ih
  | app _ _ ih₁ ih₂ => exact .app ih₁ ih₂
  | case _ _ ih ihs => exact .case ih ihs
  | unpack _ _ ih₁ ih₂ => exact .unpack ih₁ ih₂
  | pack υs _ ih => exact .pack υs ih
  | let_ _ _ ih₁ ih₂ => exact .let_ ih₁ ih₂
  | letSig _ _ ih₁ ih₂ => exact .letSig ih₁ ih₂

namespace LDomain.Lawful

variable {D : LDomain (Atom P)} (hD : D.Lawful)
include hD

/-- **Soundness of constraint generation with G_LetGen** (Lemma 6.4 for the extended
system): if `Γ ⊢ᵢ e : τ ⇝ C` (possibly using G_LetGen) and `Q_g ⊢ C` then `Q_g ; Γ ⊢ e : τ`. -/
theorem genG_sound {sig : DataSig P} {k n : Nat} {Γ : Fin n → Scheme P k} {u : Fin n → Usage}
    {e : Tm sig k n} {τ : Ty P k} {C : Wanted (Atom P) k} (hG : GenG D sig Γ u e τ C) :
    ∀ {Qg : SConstr (Atom P k)}, D.WEntails Qg C → Nonempty (HasType D sig Qg Γ u e τ) := by
  induction hG with
  | var v τs hx =>
    intro Qg h
    exact ⟨.sub (.var v τs hx) ((hD.wentails_simple_iff).mp h)⟩
  | con v T i τs =>
    intro Qg h
    exact ⟨.sub (.con v T i τs) ((hD.wentails_simple_iff).mp h)⟩
  | lam _ ih =>
    intro Qg h
    obtain ⟨d⟩ := ih h
    exact ⟨.lam d⟩
  | @app k n Γ u₁ u₂ π τ₂ τ e₁ e₂ C₁ C₂ _ _ ih₁ ih₂ =>
    intro Qg h
    have hk := hD.lawful k
    obtain ⟨A₁, E, B, hE, rfl, hA, hB⟩ := hD.inv_tensor h
    obtain ⟨B', QD, hQD, hEB, hB'⟩ := hD.wentails_scaling_inv π hB
    obtain ⟨d₁⟩ := ih₁ hA
    obtain ⟨d₂⟩ := ih₂ hB'
    refine ⟨.sub (.app d₁ d₂) ?_⟩
    refine hk.combine hE (hk.refl _) ?_
    rw [hEB]; exact hk.weaken_dup hQD (hk.refl _)
  | @case k n Γ u₁ u₂ π τ e T τs alts C Cs _ _ ih ihs =>
    intro Qg h
    have hk := hD.lawful k
    obtain ⟨A₁, E, B, hE, rfl, hA, hB⟩ := hD.inv_tensor h
    obtain ⟨A', QD, hQD, hAE, hA'⟩ := hD.wentails_scaling_inv π hA
    obtain ⟨d⟩ := ih hA'
    have hds : ∀ i, Nonempty (HasType D sig (E + B) (caseCtx sig Γ T i τs)
        (caseUsage sig π u₂ T i) (alts i) τ) :=
      fun i => ihs i (wentails_withAll hB i)
    refine ⟨.sub (.case d (fun i => Classical.choice (hds i))) ?_⟩
    refine hk.combine hE ?_ (hk.refl _)
    rw [hAE]; exact hk.weaken_dup hQD (hk.refl _)
  | @unpack k n j m Γ u₁ u₂ τ₁ mul pred ar args τ e₁ e₂ C₁ C₂ _ _ ih₁ ih₂ =>
    intro Qg h
    have hk := hD.lawful k
    obtain ⟨A₁, E, B, hE, rfl, hA, hB⟩ := hD.inv_tensor h
    obtain ⟨B', QD, hQD, hEB, hB'⟩ := hD.inv_impl hB
    obtain ⟨d₁⟩ := ih₁ hA
    obtain ⟨d₂⟩ := ih₂ hB'
    refine ⟨.sub (.unpack d₁ d₂) ?_⟩
    refine hk.combine hE (hk.refl _) ?_
    rw [hEB]; exact hk.weaken_dup hQD (hk.refl _)
  | @pack k n j m Γ u τ mul pred ar args e C υs _ ih =>
    intro Qg h
    have hk := hD.lawful k
    obtain ⟨A₁, E, B, hE, rfl, hA, hB⟩ := hD.inv_tensor h
    obtain ⟨d⟩ := ih hA
    exact ⟨.sub (.pack υs d) (hk.combine hE (hk.refl _) ((hD.wentails_simple_iff).mp hB))⟩
  | @let_ k n Γ u₁ u₂ π τ₁ τ e₁ e₂ C₁ C₂ _ _ ih₁ ih₂ =>
    intro Qg h
    have hk := hD.lawful k
    obtain ⟨A₁, E, B, hE, rfl, hA, hB⟩ := hD.inv_tensor h
    obtain ⟨A', QD, hQD, hAE, hA'⟩ := hD.wentails_scaling_inv π hA
    obtain ⟨d₁⟩ := ih₁ hA'
    obtain ⟨d₂⟩ := ih₂ hB
    have d₁' : HasType D sig (A' + 0) Γ u₁ e₁ τ₁ := (add_zero A').symm ▸ d₁
    refine ⟨.sub (.let_ d₁' d₂) ?_⟩
    refine hk.combine hE ?_ (hk.refl _)
    rw [hAE]; exact hk.weaken_dup hQD (hk.refl _)
  | @letGen k n Γ u₁ u₂ π τ₁ τ e₁ e₂ C₁ C₂ Qr Q _ hC₁ _ ih₁ ih₂ =>
    intro Qg h
    have hk := hD.lawful k
    obtain ⟨A₁, E, B, hE, rfl, hA, hB⟩ := hD.inv_tensor h
    obtain ⟨A', QD, hQD, hAE, hA'⟩ :=
      hD.wentails_scaling_inv π (C := .simple Qr) (by simpa using hA)
    have hA'Qr : (D k).Entails A' Qr := (hD.wentails_simple_iff).mp hA'
    obtain ⟨d₁⟩ := ih₁ (.dom (hk.tensor hA'Qr (hk.refl Q)) hC₁)
    obtain ⟨d₂⟩ := ih₂ hB
    refine ⟨.sub (.let_ d₁ d₂) ?_⟩
    refine hk.combine hE ?_ (hk.refl _)
    rw [hAE]; exact hk.weaken_dup hQD (hk.refl _)
  | @letSig k n Γ u₁ u₂ π σ τ e₁ e₂ C₁ C₂ _ _ ih₁ ih₂ =>
    intro Qg h
    have hk := hD.lawful k
    obtain ⟨A₁, E, B, hE, rfl, hA, hB⟩ := hD.inv_tensor h
    obtain ⟨B', QD, hQD, hEB, hB'⟩ := hD.inv_impl hB
    obtain ⟨d₁⟩ := ih₁ hB'
    obtain ⟨d₂⟩ := ih₂ hA
    refine ⟨.sub (.letSig d₁ d₂) ?_⟩
    rw [add_comm (π • B')]
    refine hk.combine hE (hk.refl _) ?_
    rw [hEB]; exact hk.weaken_dup hQD (hk.refl _)

end LDomain.Lawful

-- [NOT IN PAPER ◀ END] rule G_LetGen

end LQT
