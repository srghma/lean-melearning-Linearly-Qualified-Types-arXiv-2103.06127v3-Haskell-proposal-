module

public import RequestProject.LQT.Typing

/-!
# Constraint generation (§6.2, Figure 8)

Paper location: §6.2 "Constraint generation", Figure 8 "Constraint generation" (rules G_Var,
G_Abs, G_App, G_Pack, G_Unpack, G_Case, G_Let, G_LetSig) and Lemma 6.4 "Soundness of
constraint generation" (proof: Appendix B.6).  The start and end of each part is marked by
`-- [PAPER ▶ START]` / `-- [PAPER ◀ END]` comments.

The judgement `Γ ⊢ᵢ e : τ ⇝ C` of the paper, with `k` type variables in scope.  It reads a
typing derivation that ignores constraints (the context splittings and the types, including the
instantiations of type schemes, are given, as provided by the external type inference oracle of
the paper) and outputs the wanted constraint `C` needed to make `e` typecheck.

In rules G_Unpack and G_LetSig the fresh type variables `ā` are bound in the generated
implication constraint `π·∀ā.(Q ⊸ C)`.

The `case` rule combines the constraints of the alternatives with `&`.  For a data type with
no constructor (a case the paper does not discuss) the empty `&`-combination is taken to be
`ε`, which is sound.

We prove **Lemma 6.4 (soundness of constraint generation)**: if `Γ ⊢ᵢ e : τ ⇝ C` and
`Q_g ⊢ C` then `Q_g ; Γ ⊢ e : τ`.
-/

@[expose] public section

namespace LQT

open SConstr

variable {A : Nat → Type}

-- [PAPER ▶ START] §6.2 › Figure 8, rule G_Case: the `&`-combination of the constraints of the
--   branches (the empty combination, not discussed in the paper, is `ε`)
/-- The `&`-combination `C₀ & ⋯ & Cₘ₋₁` of a finite family of wanted constraints (`ε` when the
family is empty). -/
def withAll {k : Nat} : (m : Nat) → (Fin m → Wanted A k) → Wanted A k
  | 0, _ => .simple 0
  | 1, C => C 0
  | m + 2, C => .amp (C 0) (withAll (m + 1) (fun i => C i.succ))

-- [PAPER ◀ END] §6.2 › Figure 8, `&`-combination of rule G_Case

variable {P : Type}

-- [PAPER ▶ START] §6.2 › Figure 8 "Constraint generation": the judgement `Γ ⊢ᵢ e : τ ⇝ C` (one
--   constructor per rule; the rule name is in each docstring)
/-- The constraint generation judgement `Γ ⊢ᵢ e : τ ⇝ C` (Figure 8). -/
inductive Gen (sig : DataSig P) :
    {k n : Nat} → (Fin n → Scheme P k) → (Fin n → Usage) → Tm sig k n → Ty P k →
      Wanted (Atom P) k → Prop
  /-- G_Var -/
  | var {k n} {Γ : Fin n → Scheme P k} {x : Fin n} {σ : Scheme P k} (v : Fin n → Usage)
      (τs : Fin σ.j → Ty P k) : Γ x = σ →
      Gen sig Γ (single x + (Mult.omega : Mult) • v) (.var x) (σ.τ.subst (instSub τs))
        (.simple (σ.Q.tsubst (instSub τs)))
  -- (no separate rule in Figure 8: data constructors generate no constraint)
  /-- Data constructors (typed as unrestricted variables, with no constraint). -/
  | con {k n} {Γ : Fin n → Scheme P k} (v : Fin n → Usage) (T : Nat) (i : Fin (sig.ncons T))
      (τs : Fin (sig.params T) → Ty P k) :
      Gen sig Γ ((Mult.omega : Mult) • v) (.con T i) ((sig.conTy T i).subst τs) (.simple 0)
  /-- G_Abs -/
  | lam {k n} {Γ : Fin n → Scheme P k} {u : Fin n → Usage} {π : Mult} {τ₀ τ : Ty P k}
      {e : Tm sig k (n + 1)} {C : Wanted (Atom P) k} :
      Gen sig (Fin.cons (Scheme.mono τ₀) Γ) (Fin.cons (Usage.ofMult π) u) e τ C →
      Gen sig Γ u (.lam e) (.arr π τ₀ τ) C
  /-- G_App -/
  | app {k n} {Γ : Fin n → Scheme P k} {u₁ u₂ : Fin n → Usage} {π : Mult} {τ₂ τ : Ty P k}
      {e₁ e₂ : Tm sig k n} {C₁ C₂ : Wanted (Atom P) k} :
      Gen sig Γ u₁ e₁ (.arr π τ₂ τ) C₁ → Gen sig Γ u₂ e₂ τ₂ C₂ →
      Gen sig Γ (u₁ + π • u₂) (.app e₁ e₂) τ (.tensor C₁ (π • C₂))
  /-- G_Case -/
  | case {k n} {Γ : Fin n → Scheme P k} {u₁ u₂ : Fin n → Usage} {π : Mult} {τ : Ty P k}
      {e : Tm sig k n} {T : Nat} {τs : Fin (sig.params T) → Ty P k}
      {alts : (i : Fin (sig.ncons T)) → Tm sig k (sig.arity T i + n)}
      {C : Wanted (Atom P) k} {Cs : Fin (sig.ncons T) → Wanted (Atom P) k} :
      Gen sig Γ u₁ e (.data T (sig.params T) τs) C →
      (∀ i, Gen sig (caseCtx sig Γ T i τs) (caseUsage sig π u₂ T i) (alts i) τ (Cs i)) →
      Gen sig Γ (π • u₁ + u₂) (.case π e T alts) τ (.tensor (π • C) (withAll _ Cs))
  /-- G_Unpack -/
  | unpack {k n j m} {Γ : Fin n → Scheme P k} {u₁ u₂ : Fin n → Usage} {τ₁ : Ty P (k + j)}
      {mul : Fin m → Mult} {pred : Fin m → P} {ar : Fin m → Nat}
      {args : (i : Fin m) → Fin (ar i) → Ty P (k + j)} {τ : Ty P k}
      {e₁ : Tm sig k n} {e₂ : Tm sig (k + j) (n + 1)} {C₁ : Wanted (Atom P) k}
      {C₂ : Wanted (Atom P) (k + j)} :
      Gen sig Γ u₁ e₁ (.exq j τ₁ m mul pred ar args) C₁ →
      Gen sig (Fin.cons (Scheme.mono τ₁) (ctxWk j Γ)) (Fin.cons Usage.one u₂) e₂ (τ.wk j) C₂ →
      Gen sig Γ (u₁ + u₂) (.unpack j e₁ e₂) τ
        (.tensor C₁ (.impl .one j (exqC m mul pred ar args) C₂))
  /-- G_Pack -/
  | pack {k n j m} {Γ : Fin n → Scheme P k} {u : Fin n → Usage} {τ : Ty P (k + j)}
      {mul : Fin m → Mult} {pred : Fin m → P} {ar : Fin m → Nat}
      {args : (i : Fin m) → Fin (ar i) → Ty P (k + j)} {e : Tm sig k n}
      {C : Wanted (Atom P) k} (υs : Fin j → Ty P k) :
      Gen sig Γ u e (τ.subst (instSub υs)) C →
      Gen sig Γ u (.pack e) (.exq j τ m mul pred ar args)
        (.tensor C (.simple ((exqC m mul pred ar args).tsubst (instSub υs))))
  /-- G_Let -/
  | let_ {k n} {Γ : Fin n → Scheme P k} {u₁ u₂ : Fin n → Usage} {π : Mult} {τ₁ τ : Ty P k}
      {e₁ : Tm sig k n} {e₂ : Tm sig k (n + 1)} {C₁ C₂ : Wanted (Atom P) k} :
      Gen sig Γ u₁ e₁ τ₁ C₁ →
      Gen sig (Fin.cons (Scheme.mono τ₁) Γ) (Fin.cons (Usage.ofMult π) u₂) e₂ τ C₂ →
      Gen sig Γ (π • u₁ + u₂) (.let_ π e₁ e₂) τ (.tensor (π • C₁) C₂)
  /-- G_LetSig -/
  | letSig {k n} {Γ : Fin n → Scheme P k} {u₁ u₂ : Fin n → Usage} {π : Mult} {σ : Scheme P k}
      {τ : Ty P k} {e₁ : Tm sig (k + σ.j) n} {e₂ : Tm sig k (n + 1)}
      {C₁ : Wanted (Atom P) (k + σ.j)} {C₂ : Wanted (Atom P) k} :
      Gen sig (ctxWk σ.j Γ) u₁ e₁ σ.τ C₁ →
      Gen sig (Fin.cons σ Γ) (Fin.cons (Usage.ofMult π) u₂) e₂ τ C₂ →
      Gen sig Γ (π • u₁ + u₂) (.letSig π σ e₁ e₂) τ (.tensor C₂ (.impl π σ.j σ.Q C₁))

-- [PAPER ◀ END] §6.2 › Figure 8

namespace LDomain.Lawful

section

variable [∀ k, DecidableEq (A k)] [Weakening A] {D : LDomain A}

-- [NOT IN PAPER ▶ START] helper: inversion of an `&`-combination
/-- Each component of an `&`-combination is entailed. -/
lemma wentails_withAll {k : Nat} {Q : SConstr (A k)} :
    ∀ {m : Nat} {Cs : Fin m → Wanted A k}, D.WEntails Q (withAll m Cs) → ∀ i, D.WEntails Q (Cs i)
  | 0, _, _, i => i.elim0
  | 1, Cs, h, i => by
    have : i = 0 := Subsingleton.elim _ _
    subst this; exact h
  | m + 2, Cs, h, i => by
    obtain ⟨h₁, h₂⟩ := LDomain.Lawful.inv_amp h
    refine Fin.cases h₁ (fun j => ?_) i
    exact wentails_withAll (Cs := fun i => Cs i.succ) h₂ j

-- [NOT IN PAPER ◀ END] helper

end

variable {D : LDomain (Atom P)} (hD : D.Lawful)
include hD

-- [PAPER ▶ START] §6.2 › Lemma 6.4 "Soundness of constraint generation" (proof: Appendix B.6)
/-- **Lemma 6.4 (Soundness of constraint generation).** For all `Q_g`, if `Γ ⊢ᵢ e : τ ⇝ C`
and `Q_g ⊢ C` then `Q_g ; Γ ⊢ e : τ`. -/
theorem gen_sound {sig : DataSig P} {k n : Nat} {Γ : Fin n → Scheme P k} {u : Fin n → Usage}
    {e : Tm sig k n} {τ : Ty P k} {C : Wanted (Atom P) k} (hG : Gen sig Γ u e τ C) :
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

-- [PAPER ◀ END] §6.2 › Lemma 6.4

end LDomain.Lawful

end LQT
