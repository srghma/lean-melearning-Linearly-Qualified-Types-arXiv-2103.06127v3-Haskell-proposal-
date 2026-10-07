module

public import RequestProject.LQT.Ch5_QualifiedTypeSystem.Syntax

/-!
# The qualified type system (§5.2, Figure 6)

Paper location: §5.2 "Typing rules", Figure 6 "Qualified type system" (rules E_Var, E_Abs,
E_App, E_Pack, E_Unpack, E_Let, E_LetSig, E_Case, E_Sub); context scaling and addition are
defined below the grammar in Figure 5.  The start and end of the figure is marked by
`-- [PAPER ▶ START]` / `-- [PAPER ◀ END]` comments.

The judgement `Q ; Γ ⊢ e : τ` of the paper, with `k` type variables in scope.  In the de Bruijn
presentation, a context of the paper is split into the type schemes of all the variables in
scope, `Γ : Fin n → Scheme P k`, and a *usage vector* `u : Fin n → Usage` giving the
multiplicity of each variable (`0` for a variable that does not occur in the paper's context).
Context addition `Γ₁ + Γ₂` and scaling `π · Γ` are pointwise addition and scaling of usage
vectors (contexts that are added always agree on types, as required in the paper).

The judgement is `Type`-valued: the desugaring of §7 is defined by recursion on typing
derivations, exactly as in the paper.

The constraint domain is a family `D : LDomain (Atom P)` of domains, one for each number of
type variables in scope.  The freshness conditions "`ā` fresh" of rules E_Unpack and E_LetSig
are expressed by working in the scope extended with the `j` new type variables, in which the
rest of the context, the other constraints and the result type are weakened (`ctxWk`,
`SConstr.wk`, `Ty.wk`).

Rules:
* E_Var: `Γ x = ∀ā. Q ⇒ υ` gives `Q[τ̄/ā] ; Γ, (x ↦ 1) + ω·v ⊢ x : υ[τ̄/ā]`;
* data constructors are typed like unrestricted variables of type `∀ā. ῡ →_π̄ T ā` (E_Con);
* E_Abs, E_App, E_Pack, E_Unpack, E_Let, E_LetSig, E_Case, E_Sub as in the paper.
-/

@[expose] public section

namespace LQT

variable {P : Type}

-- [PAPER ▶ START] §5.2 › Figure 6 "Qualified type system": the judgement `Q ; Γ ⊢ e : τ` (one
--   constructor per rule; the rule name is in each docstring)
/-- The typing judgement `Q ; Γ ⊢ e : τ` of the qualified type system, for the family of
constraint domains `D` and the data type signature `sig`. -/
inductive HasType (D : LDomain (Atom P)) (sig : DataSig P) :
    {k n : Nat} → SConstr (Atom P k) → (Fin n → Scheme P k) → (Fin n → Usage) → Tm sig k n →
      Ty P k → Type
  /-- E_Var -/
  | var {k n} {Γ : Fin n → Scheme P k} {x : Fin n} {σ : Scheme P k} (v : Fin n → Usage)
      (τs : Fin σ.j → Ty P k) : Γ x = σ →
      HasType D sig (σ.Q.tsubst (instSub τs)) Γ (single x + (Mult.omega : Mult) • v) (.var x)
        (σ.τ.subst (instSub τs))
  -- (no separate rule in Figure 6: data constructors `K` are typed like unrestricted variables)
  /-- Data constructors are typed as unrestricted variables. -/
  | con {k n} {Γ : Fin n → Scheme P k} (v : Fin n → Usage) (T : Nat) (i : Fin (sig.ncons T))
      (τs : Fin (sig.params T) → Ty P k) :
      HasType D sig 0 Γ ((Mult.omega : Mult) • v) (.con T i) ((sig.conTy T i).subst τs)
  /-- E_Abs -/
  | lam {k n} {Q : SConstr (Atom P k)} {Γ : Fin n → Scheme P k} {u : Fin n → Usage} {π : Mult}
      {τ₁ τ₂ : Ty P k} {e : Tm sig k (n + 1)} :
      HasType D sig Q (Fin.cons (Scheme.mono τ₁) Γ) (Fin.cons (Usage.ofMult π) u) e τ₂ →
      HasType D sig Q Γ u (.lam e) (.arr π τ₁ τ₂)
  /-- E_App -/
  | app {k n} {Q₁ Q₂ : SConstr (Atom P k)} {Γ : Fin n → Scheme P k} {u₁ u₂ : Fin n → Usage}
      {π : Mult} {τ₁ τ : Ty P k} {e₁ e₂ : Tm sig k n} :
      HasType D sig Q₁ Γ u₁ e₁ (.arr π τ₁ τ) → HasType D sig Q₂ Γ u₂ e₂ τ₁ →
      HasType D sig (Q₁ + π • Q₂) Γ (u₁ + π • u₂) (.app e₁ e₂) τ
  /-- E_Pack -/
  | pack {k n j m} {Q : SConstr (Atom P k)} {Γ : Fin n → Scheme P k} {u : Fin n → Usage}
      {τ : Ty P (k + j)} {mul : Fin m → Mult} {pred : Fin m → P} {ar : Fin m → Nat}
      {args : (i : Fin m) → Fin (ar i) → Ty P (k + j)} {e : Tm sig k n} (υs : Fin j → Ty P k) :
      HasType D sig Q Γ u e (τ.subst (instSub υs)) →
      HasType D sig (Q + (exqC m mul pred ar args).tsubst (instSub υs)) Γ u (.pack e)
        (.exq j τ m mul pred ar args)
  /-- E_Unpack -/
  | unpack {k n j m} {Q₁ Q₂ : SConstr (Atom P k)} {Γ : Fin n → Scheme P k}
      {u₁ u₂ : Fin n → Usage} {τ₁ : Ty P (k + j)} {mul : Fin m → Mult} {pred : Fin m → P}
      {ar : Fin m → Nat} {args : (i : Fin m) → Fin (ar i) → Ty P (k + j)} {τ : Ty P k}
      {e₁ : Tm sig k n} {e₂ : Tm sig (k + j) (n + 1)} :
      HasType D sig Q₁ Γ u₁ e₁ (.exq j τ₁ m mul pred ar args) →
      HasType D sig (Q₂.wk j + exqC m mul pred ar args) (Fin.cons (Scheme.mono τ₁) (ctxWk j Γ))
        (Fin.cons Usage.one u₂) e₂ (τ.wk j) →
      HasType D sig (Q₁ + Q₂) Γ (u₁ + u₂) (.unpack j e₁ e₂) τ
  /-- E_Let -/
  | let_ {k n} {Q Q₁ Q₂ : SConstr (Atom P k)} {Γ : Fin n → Scheme P k} {u₁ u₂ : Fin n → Usage}
      {π : Mult} {τ₁ τ : Ty P k} {e₁ : Tm sig k n} {e₂ : Tm sig k (n + 1)} :
      HasType D sig (Q₁ + Q) Γ u₁ e₁ τ₁ →
      HasType D sig Q₂ (Fin.cons ⟨0, Q, τ₁⟩ Γ) (Fin.cons (Usage.ofMult π) u₂) e₂ τ →
      HasType D sig (π • Q₁ + Q₂) Γ (π • u₁ + u₂) (.let_ π e₁ e₂) τ
  /-- E_LetSig -/
  | letSig {k n} {Q₁ Q₂ : SConstr (Atom P k)} {Γ : Fin n → Scheme P k} {u₁ u₂ : Fin n → Usage}
      {π : Mult} {σ : Scheme P k} {τ : Ty P k} {e₁ : Tm sig (k + σ.j) n}
      {e₂ : Tm sig k (n + 1)} :
      HasType D sig (Q₁.wk σ.j + σ.Q) (ctxWk σ.j Γ) u₁ e₁ σ.τ →
      HasType D sig Q₂ (Fin.cons σ Γ) (Fin.cons (Usage.ofMult π) u₂) e₂ τ →
      HasType D sig (π • Q₁ + Q₂) Γ (π • u₁ + u₂) (.letSig π σ e₁ e₂) τ
  /-- E_Case -/
  | case {k n} {Q₁ Q₂ : SConstr (Atom P k)} {Γ : Fin n → Scheme P k} {u₁ u₂ : Fin n → Usage}
      {π : Mult} {τ : Ty P k} {e : Tm sig k n} {T : Nat} {τs : Fin (sig.params T) → Ty P k}
      {alts : (i : Fin (sig.ncons T)) → Tm sig k (sig.arity T i + n)} :
      HasType D sig Q₁ Γ u₁ e (.data T (sig.params T) τs) →
      ((i : Fin (sig.ncons T)) →
        HasType D sig Q₂ (caseCtx sig Γ T i τs) (caseUsage sig π u₂ T i) (alts i) τ) →
      HasType D sig (π • Q₁ + Q₂) Γ (π • u₁ + u₂) (.case π e T alts) τ
  /-- E_Sub -/
  | sub {k n} {Q Q₁ : SConstr (Atom P k)} {Γ : Fin n → Scheme P k} {u : Fin n → Usage}
      {τ : Ty P k} {e : Tm sig k n} :
      HasType D sig Q₁ Γ u e τ → (D k).Entails Q Q₁ → HasType D sig Q Γ u e τ

-- [PAPER ◀ END] §5.2 › Figure 6

end LQT
