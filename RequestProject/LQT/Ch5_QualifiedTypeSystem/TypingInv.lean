module

public import RequestProject.LQT.Ch5_QualifiedTypeSystem.Typing

/-!
# Inversion ("generation") lemmas for the qualified type system

Paper location: none.  The paper does not state these lemmas; they are the standard inversion
principles for the syntax-directed rules of Figure 6 in the presence of the non-syntax-directed
rule E_Sub.  For each syntactic form, a derivation of `Q ; Γ ⊢ e : τ` consists of a chain of
E_Sub steps above an instance of the rule for that form; composing the entailments of the chain
(law (1)/(2) of Figure 4, i.e. transitivity) gives the statements below.

They are used in `Ch3_LinearConstraints/MinimalExamples.lean` (and the other example files)
to show that the ill-behaved programs of §3.1 are rejected.
-/

@[expose] public section

namespace LQT

-- [NOT IN PAPER ▶ START] inversion lemmas for the typing rules of Figure 6 (whole file)

namespace HasType

variable {P : Type} {D : LDomain (Atom P)} {sig : DataSig P}

/-- Inversion for variables (rule E_Var, below E_Sub steps). -/
theorem var_inv (hD : ∀ k, (D k).Lawful) {k n : Nat} {Q : SConstr (Atom P k)}
    {Γ : Fin n → Scheme P k} {u : Fin n → Usage} {x : Fin n} {τ : Ty P k}
    (d : HasType D sig Q Γ u (.var x) τ) :
    ∃ τs : Fin (Γ x).j → Ty P k, (D k).Entails Q ((Γ x).Q.tsubst (instSub τs)) ∧
      τ = (Γ x).τ.subst (instSub τs) := by
  generalize he : (Tm.var x : Tm sig k n) = e at d
  induction d with
  | var v τs hx =>
    cases he; subst hx
    exact ⟨τs, (hD _).refl _, rfl⟩
  | sub _ h ih =>
    obtain ⟨τs, h₁, h₂⟩ := ih he
    exact ⟨τs, (hD _).trans h h₁, h₂⟩
  | _ => cases he

/-- Inversion for data constructors (below E_Sub steps). -/
theorem con_inv (hD : ∀ k, (D k).Lawful) {k n : Nat} {Q : SConstr (Atom P k)}
    {Γ : Fin n → Scheme P k} {u : Fin n → Usage} {T : Nat} {i : Fin (sig.ncons T)}
    {τ : Ty P k} (d : HasType D sig Q Γ u (.con T i) τ) :
    ∃ τs : Fin (sig.params T) → Ty P k, (D k).Entails Q 0 ∧ τ = (sig.conTy T i).subst τs := by
  generalize he : (Tm.con T i : Tm sig k n) = e at d
  induction d with
  | con v T' i' τs =>
    cases he
    exact ⟨τs, (hD _).refl _, rfl⟩
  | sub _ h ih =>
    obtain ⟨τs, h₁, h₂⟩ := ih he
    exact ⟨τs, (hD _).trans h h₁, h₂⟩
  | _ => cases he

/-- Inversion for abstractions (rule E_Abs, below E_Sub steps). -/
theorem lam_inv (hD : ∀ k, (D k).Lawful) {k n : Nat} {Q : SConstr (Atom P k)}
    {Γ : Fin n → Scheme P k} {u : Fin n → Usage} {e : Tm sig k (n + 1)} {τ : Ty P k}
    (d : HasType D sig Q Γ u (.lam e) τ) :
    ∃ (Q' : SConstr (Atom P k)) (π : Mult) (τ₁ τ₂ : Ty P k), (D k).Entails Q Q' ∧
      τ = .arr π τ₁ τ₂ ∧
      Nonempty (HasType D sig Q' (Fin.cons (Scheme.mono τ₁) Γ) (Fin.cons (Usage.ofMult π) u)
        e τ₂) := by
  generalize he : (Tm.lam e : Tm sig k n) = e' at d
  induction d with
  | lam d _ =>
    cases he
    exact ⟨_, _, _, _, (hD _).refl _, rfl, ⟨d⟩⟩
  | sub _ h ih =>
    obtain ⟨Q', π, τ₁, τ₂, h₁, h₂, h₃⟩ := ih he
    exact ⟨Q', π, τ₁, τ₂, (hD _).trans h h₁, h₂, h₃⟩
  | _ => cases he

/-- Inversion for applications (rule E_App, below E_Sub steps). -/
theorem app_inv (hD : ∀ k, (D k).Lawful) {k n : Nat} {Q : SConstr (Atom P k)}
    {Γ : Fin n → Scheme P k} {u : Fin n → Usage} {e₁ e₂ : Tm sig k n} {τ : Ty P k}
    (d : HasType D sig Q Γ u (.app e₁ e₂) τ) :
    ∃ (Q₁ Q₂ : SConstr (Atom P k)) (u₁ u₂ : Fin n → Usage) (π : Mult) (τ₁ : Ty P k),
      (D k).Entails Q (Q₁ + π • Q₂) ∧ Nonempty (HasType D sig Q₁ Γ u₁ e₁ (.arr π τ₁ τ)) ∧
      Nonempty (HasType D sig Q₂ Γ u₂ e₂ τ₁) := by
  generalize he : (Tm.app e₁ e₂ : Tm sig k n) = e at d
  induction d with
  | app d₁ d₂ _ _ =>
    cases he
    exact ⟨_, _, _, _, _, _, (hD _).refl _, ⟨d₁⟩, ⟨d₂⟩⟩
  | sub _ h ih =>
    obtain ⟨Q₁, Q₂, u₁, u₂, π, τ₁, h₁, h₂, h₃⟩ := ih he
    exact ⟨Q₁, Q₂, u₁, u₂, π, τ₁, (hD _).trans h h₁, h₂, h₃⟩
  | _ => cases he

/-- Inversion for `case` expressions (rule E_Case, below E_Sub steps). -/
theorem case_inv (hD : ∀ k, (D k).Lawful) {k n : Nat} {Q : SConstr (Atom P k)}
    {Γ : Fin n → Scheme P k} {u : Fin n → Usage} {π : Mult} {e : Tm sig k n} {T : Nat}
    {alts : (i : Fin (sig.ncons T)) → Tm sig k (sig.arity T i + n)} {τ : Ty P k}
    (d : HasType D sig Q Γ u (.case π e T alts) τ) :
    ∃ (Q₁ Q₂ : SConstr (Atom P k)) (u₁ u₂ : Fin n → Usage)
      (τs : Fin (sig.params T) → Ty P k),
      (D k).Entails Q (π • Q₁ + Q₂) ∧
      Nonempty (HasType D sig Q₁ Γ u₁ e (.data T (sig.params T) τs)) ∧
      ∀ i, Nonempty (HasType D sig Q₂ (caseCtx sig Γ T i τs) (caseUsage sig π u₂ T i)
        (alts i) τ) := by
  generalize he : (Tm.case π e T alts : Tm sig k n) = e' at d
  induction d with
  | case d ds _ _ =>
    cases he
    exact ⟨_, _, _, _, _, (hD _).refl _, ⟨d⟩, fun i => ⟨ds i⟩⟩
  | sub _ h ih =>
    obtain ⟨Q₁, Q₂, u₁, u₂, τs, h₁, h₂, h₃⟩ := ih he
    exact ⟨Q₁, Q₂, u₁, u₂, τs, (hD _).trans h h₁, h₂, h₃⟩
  | _ => cases he

end HasType

-- [NOT IN PAPER ◀ END] inversion lemmas

end LQT
