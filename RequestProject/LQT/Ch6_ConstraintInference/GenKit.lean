module

public import RequestProject.LQT.Ch6_ConstraintInference.Generation

/-!
# Building constraint-generation derivations for concrete programs

Paper location: none.  This file provides tools to write down constraint-generation
derivations (Figure 8) for the larger example programs of §3.2, §4 and §6.3.2.

* `Gen.weaken`: the usage of any variable can be increased by an unrestricted amount
  (`u ↦ u + ω·v`).  In the paper this is the implicit weakening of unrestricted variables
  allowed by rule G_Var (`Γ, x :₁ σ + ω·Γ'`); it is admissible for the whole judgement.
* `Gen.weakenTo`: the pointwise form used in practice: every usage may stay the same or become
  `ω`.
* Variants of the rules whose conclusions are stated with computable usages
  (`Gen.var'`, `Gen.con'`, `Gen.lam'`, `Gen.let'`, `Gen.unpack'`, `Gen.letSig'`, `Gen.case'`),
  so that the side conditions can be discharged by `decide`.
-/

@[expose] public section

namespace LQT

variable {P : Type} {sig : DataSig P}

-- [NOT IN PAPER ▶ START] tools to build constraint-generation derivations (whole file)

/-- Weakening of the usage of unrestricted variables is admissible for constraint
generation. -/
theorem Gen.weaken {k n : Nat} {Γ : Fin n → Scheme P k} {u : Fin n → Usage} {e : Tm sig k n}
    {τ : Ty P k} {C : Wanted (Atom P) k} (g : Gen sig Γ u e τ C) :
    ∀ v : Fin n → Usage, Gen sig Γ (u + (Mult.omega : Mult) • v) e τ C := by
  induction g with
  | var v₀ τs hx =>
    intro v
    have := Gen.var (sig := sig) (v₀ + v) τs hx
    rwa [smul_add, ← add_assoc] at this
  | @con k n Γ v₀ T i τs =>
    intro v
    have := Gen.con (sig := sig) (Γ := Γ) (v₀ + v) T i τs
    rwa [smul_add] at this
  | @lam k n Γ u π τ₀ τ e C _ ih =>
    intro v
    have h := ih (Fin.cons 0 v)
    have e' : (Fin.cons (Usage.ofMult π) u : Fin (n + 1) → Usage) +
        (Mult.omega : Mult) • (Fin.cons 0 v : Fin (n + 1) → Usage) =
        Fin.cons (Usage.ofMult π) (u + (Mult.omega : Mult) • v) := by
      funext x; refine Fin.cases ?_ (fun y => ?_) x <;> simp
    rw [e'] at h
    exact .lam h
  | @app k n Γ u₁ u₂ π τ₂ τ e₁ e₂ C₁ C₂ _ _ ih₁ _ =>
    intro v
    have h := Gen.app (ih₁ v) ‹Gen sig Γ u₂ e₂ τ₂ C₂›
    have e' : u₁ + (Mult.omega : Mult) • v + π • u₂ = u₁ + π • u₂ + (Mult.omega : Mult) • v := by
      abel
    rwa [e'] at h
  | @case k n Γ u₁ u₂ π τ e T τs alts C Cs g₁ gs _ ihs =>
    intro v
    have hs : ∀ i, Gen sig (caseCtx sig Γ T i τs)
        (caseUsage sig π (u₂ + (Mult.omega : Mult) • v) T i) (alts i) τ (Cs i) := by
      intro i
      have h := ihs i (Fin.append 0 v)
      have e' : caseUsage sig π u₂ T i + (Mult.omega : Mult) • Fin.append 0 v =
          caseUsage sig π (u₂ + (Mult.omega : Mult) • v) T i := by
        funext x
        refine Fin.addCases (fun l => ?_) (fun y => ?_) x <;> simp [caseUsage]
      rwa [e'] at h
    have h := Gen.case g₁ hs
    rwa [← add_assoc] at h
  | @unpack k n j m Γ u₁ u₂ τ₁ mul pred ar args τ e₁ e₂ C₁ C₂ g₁ _ _ ih₂ =>
    intro v
    have h := ih₂ (Fin.cons 0 v)
    have e' : (Fin.cons Usage.one u₂ : Fin (n + 1) → Usage) +
        (Mult.omega : Mult) • (Fin.cons 0 v : Fin (n + 1) → Usage) =
        Fin.cons Usage.one (u₂ + (Mult.omega : Mult) • v) := by
      funext x; refine Fin.cases ?_ (fun y => ?_) x <;> simp
    rw [e'] at h
    have h' := Gen.unpack g₁ h
    rwa [← add_assoc] at h'
  | @pack k n j m Γ u τ mul pred ar args e C υs _ ih =>
    intro v
    exact .pack υs (ih v)
  | @let_ k n Γ u₁ u₂ π τ₁ τ e₁ e₂ C₁ C₂ g₁ _ _ ih₂ =>
    intro v
    have h := ih₂ (Fin.cons 0 v)
    have e' : (Fin.cons (Usage.ofMult π) u₂ : Fin (n + 1) → Usage) +
        (Mult.omega : Mult) • (Fin.cons 0 v : Fin (n + 1) → Usage) =
        Fin.cons (Usage.ofMult π) (u₂ + (Mult.omega : Mult) • v) := by
      funext x; refine Fin.cases ?_ (fun y => ?_) x <;> simp
    rw [e'] at h
    have h' := Gen.let_ g₁ h
    rwa [← add_assoc] at h'
  | @letSig k n Γ u₁ u₂ π σ τ e₁ e₂ C₁ C₂ g₁ _ _ ih₂ =>
    intro v
    have h := ih₂ (Fin.cons 0 v)
    have e' : (Fin.cons (Usage.ofMult π) u₂ : Fin (n + 1) → Usage) +
        (Mult.omega : Mult) • (Fin.cons 0 v : Fin (n + 1) → Usage) =
        Fin.cons (Usage.ofMult π) (u₂ + (Mult.omega : Mult) • v) := by
      funext x; refine Fin.cases ?_ (fun y => ?_) x <;> simp
    rw [e'] at h
    have h' := Gen.letSig g₁ h
    rwa [← add_assoc] at h'

/-- `u'` is obtained from `u` by turning some usages into `ω`. -/
def UsageLE {n : Nat} (u u' : Fin n → Usage) : Prop := ∀ x, u' x = u x ∨ u' x = Usage.omega

instance {n : Nat} (u u' : Fin n → Usage) : Decidable (UsageLE u u') := by
  unfold UsageLE; infer_instance

/-- Pointwise weakening: usages may be turned into `ω`. -/
theorem Gen.weakenTo {k n : Nat} {Γ : Fin n → Scheme P k} {u u' : Fin n → Usage}
    {e : Tm sig k n} {τ : Ty P k} {C : Wanted (Atom P) k} (g : Gen sig Γ u e τ C)
    (h : UsageLE u u') : Gen sig Γ u' e τ C := by
  classical
  have e' : u' = u + (Mult.omega : Mult) • (fun x => if u' x = u x then 0 else Usage.one) := by
    funext x
    rcases h x with hx | hx
    · simp [hx]
    · by_cases hx' : u' x = u x
      · simp [hx']
      · have hne : ¬ u' x = u x := hx'
        show u' x = u x + (Mult.omega : Mult) • (if u' x = u x then 0 else Usage.one)
        rw [if_neg hne, hx]; cases u x <;> rfl
  rw [e']; exact g.weaken _

/-- G_Var with the usage `single x` and the type and constraint given up to equality. -/
theorem Gen.var' {k n : Nat} {Γ : Fin n → Scheme P k} (x : Fin n) (τs : Fin (Γ x).j → Ty P k)
    {τ : Ty P k} {Q : SConstr (Atom P k)} (hτ : (Γ x).τ.subst (instSub τs) = τ)
    (hQ : (Γ x).Q.tsubst (instSub τs) = Q) : Gen sig Γ (single x) (.var x) τ (.simple Q) := by
  have := Gen.var (sig := sig) (Γ := Γ) (x := x) 0 τs rfl
  rw [smul_zero, add_zero, hτ, hQ] at this
  exact this

/-- Data constructors, with the usage `0` and the type given up to equality. -/
theorem Gen.con' {k n : Nat} {Γ : Fin n → Scheme P k} (T : Nat) (i : Fin (sig.ncons T))
    (τs : Fin (sig.params T) → Ty P k) {τ : Ty P k} (hτ : (sig.conTy T i).subst τs = τ) :
    Gen sig Γ 0 (.con T i) τ (.simple 0) := by
  have := Gen.con (sig := sig) (Γ := Γ) 0 T i τs
  rwa [smul_zero, hτ] at this

/-- The usage `u` of a body is compatible with binding its variable `0` at multiplicity `π`. -/
def BindOK {n : Nat} (π : Mult) (u : Fin (n + 1) → Usage) : Prop :=
  u 0 = Usage.ofMult π ∨ π = .omega

instance {n : Nat} (π : Mult) (u : Fin (n + 1) → Usage) : Decidable (BindOK π u) := by
  unfold BindOK; infer_instance

lemma BindOK.usageLE {n : Nat} {π : Mult} {u : Fin (n + 1) → Usage} (h : BindOK π u) :
    UsageLE u (Fin.cons (Usage.ofMult π) (Fin.tail u)) := by
  intro x
  refine Fin.cases ?_ (fun y => ?_) x
  · rcases h with h | rfl
    · simp [h]
    · simp
  · simp [Fin.tail]

/-- G_Abs, with the usage of the body given by its derivation. -/
theorem Gen.lam' {k n : Nat} {Γ : Fin n → Scheme P k} {u : Fin (n + 1) → Usage} {π : Mult}
    {τ₀ τ : Ty P k} {e : Tm sig k (n + 1)} {C : Wanted (Atom P) k}
    (g : Gen sig (Fin.cons (Scheme.mono τ₀) Γ) u e τ C) (h : BindOK π u) :
    Gen sig Γ (Fin.tail u) (.lam e) (.arr π τ₀ τ) C :=
  .lam (g.weakenTo h.usageLE)

/-- G_Let, with the usage of the body given by its derivation. -/
theorem Gen.let' {k n : Nat} {Γ : Fin n → Scheme P k} {u₁ : Fin n → Usage}
    {u₂ : Fin (n + 1) → Usage} {π : Mult} {τ₁ τ : Ty P k} {e₁ : Tm sig k n}
    {e₂ : Tm sig k (n + 1)} {C₁ C₂ : Wanted (Atom P) k} (g₁ : Gen sig Γ u₁ e₁ τ₁ C₁)
    (g₂ : Gen sig (Fin.cons (Scheme.mono τ₁) Γ) u₂ e₂ τ C₂) (h : BindOK π u₂) :
    Gen sig Γ (π • u₁ + Fin.tail u₂) (.let_ π e₁ e₂) τ (.tensor (π • C₁) C₂) :=
  .let_ g₁ (g₂.weakenTo h.usageLE)

/-- G_Unpack, with the usage of the body given by its derivation and its type given up to
equality. -/
theorem Gen.unpack' {k n j m : Nat} {Γ : Fin n → Scheme P k} {u₁ : Fin n → Usage}
    {u₂ : Fin (n + 1) → Usage} {τ₁ : Ty P (k + j)} {mul : Fin m → Mult} {pred : Fin m → P}
    {ar : Fin m → Nat} {args : (i : Fin m) → Fin (ar i) → Ty P (k + j)} {τ : Ty P k}
    {τ' : Ty P (k + j)} {e₁ : Tm sig k n} {e₂ : Tm sig (k + j) (n + 1)}
    {C₁ : Wanted (Atom P) k} {C₂ : Wanted (Atom P) (k + j)}
    (g₁ : Gen sig Γ u₁ e₁ (.exq j τ₁ m mul pred ar args) C₁) (hτ : τ.wk j = τ')
    (g₂ : Gen sig (Fin.cons (Scheme.mono τ₁) (ctxWk j Γ)) u₂ e₂ τ' C₂)
    (h : BindOK .one u₂) :
    Gen sig Γ (u₁ + Fin.tail u₂) (.unpack j e₁ e₂) τ
      (.tensor C₁ (.impl .one j (exqC m mul pred ar args) C₂)) := by
  subst hτ
  exact .unpack g₁ (g₂.weakenTo h.usageLE)

/-- G_Pack, with the type of the packed expression given up to equality. -/
theorem Gen.pack' {k n j m : Nat} {Γ : Fin n → Scheme P k} {u : Fin n → Usage}
    {τ : Ty P (k + j)} {mul : Fin m → Mult} {pred : Fin m → P} {ar : Fin m → Nat}
    {args : (i : Fin m) → Fin (ar i) → Ty P (k + j)} {e : Tm sig k n} {τ' : Ty P k}
    {C : Wanted (Atom P) k} (υs : Fin j → Ty P k) (hτ : τ.subst (instSub υs) = τ')
    (g : Gen sig Γ u e τ' C) :
    Gen sig Γ u (.pack e) (.exq j τ m mul pred ar args)
      (.tensor C (.simple ((exqC m mul pred ar args).tsubst (instSub υs)))) := by
  subst hτ
  exact .pack υs g

/-- G_LetSig, with the usage of the body given by its derivation. -/
theorem Gen.letSig' {k n : Nat} {Γ : Fin n → Scheme P k} {u₁ : Fin n → Usage}
    {u₂ : Fin (n + 1) → Usage} {π : Mult} {σ : Scheme P k} {τ : Ty P k}
    {e₁ : Tm sig (k + σ.j) n} {e₂ : Tm sig k (n + 1)} {C₁ : Wanted (Atom P) (k + σ.j)}
    {C₂ : Wanted (Atom P) k} (g₁ : Gen sig (ctxWk σ.j Γ) u₁ e₁ σ.τ C₁)
    (g₂ : Gen sig (Fin.cons σ Γ) u₂ e₂ τ C₂) (h : BindOK π u₂) :
    Gen sig Γ (π • u₁ + Fin.tail u₂) (.letSig π σ e₁ e₂) τ (.tensor C₂ (.impl π σ.j σ.Q C₁)) :=
  .letSig g₁ (g₂.weakenTo h.usageLE)

/-- The usage, in the enclosing context, of a `case` whose alternatives have usages `U i`:
a variable gets `0` (resp. `1`) if all alternatives give it `0` (resp. `1`), and `ω`
otherwise. -/
def caseJoin {n : Nat} (T : Nat) (U : (i : Fin (sig.ncons T)) → Fin (sig.arity T i + n) → Usage) :
    Fin n → Usage := fun x =>
  if ∀ i, U i (Fin.natAdd _ x) = 0 then 0
  else if ∀ i, U i (Fin.natAdd _ x) = Usage.one then Usage.one else Usage.omega

/-- G_Case, with the usages of the alternatives given by their derivations. -/
theorem Gen.case' {k n : Nat} {Γ : Fin n → Scheme P k} {u₁ : Fin n → Usage} {π : Mult}
    {τ : Ty P k} {e : Tm sig k n} {T : Nat} {τs : Fin (sig.params T) → Ty P k}
    {alts : (i : Fin (sig.ncons T)) → Tm sig k (sig.arity T i + n)}
    {C : Wanted (Atom P) k} {Cs : Fin (sig.ncons T) → Wanted (Atom P) k}
    {U : (i : Fin (sig.ncons T)) → Fin (sig.arity T i + n) → Usage}
    (g : Gen sig Γ u₁ e (.data T (sig.params T) τs) C)
    (gs : ∀ i, Gen sig (caseCtx sig Γ T i τs) (U i) (alts i) τ (Cs i))
    (h : ∀ i, UsageLE (U i) (caseUsage sig π (caseJoin T U) T i)) :
    Gen sig Γ (π • u₁ + caseJoin T U) (.case π e T alts) τ (.tensor (π • C) (withAll _ Cs)) :=
  .case g (fun i => (gs i).weakenTo (h i))

/-- Recasting a derivation along equalities of usage, type and constraint. -/
theorem Gen.cast {k n : Nat} {Γ : Fin n → Scheme P k} {u u' : Fin n → Usage} {e : Tm sig k n}
    {τ τ' : Ty P k} {C C' : Wanted (Atom P) k} (g : Gen sig Γ u e τ C) (hu : u = u')
    (hτ : τ = τ') (hC : C = C') : Gen sig Γ u' e τ' C' := by
  subst hu hτ hC; exact g

-- [NOT IN PAPER ◀ END] tools to build constraint-generation derivations

end LQT
