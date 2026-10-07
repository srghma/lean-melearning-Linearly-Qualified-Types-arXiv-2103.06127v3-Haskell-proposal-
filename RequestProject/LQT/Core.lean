module

public import RequestProject.LQT.Typing

/-!
# The core calculus (§7.1, Figure 11, Appendix A.1)

Paper location: §7.1 "The core calculus" (Figure 11 "Core calculus (subset)"), its complete
version in Appendix A.1 (Figure 13 "Grammar of the core calculus", Figure 14 "Core calculus
type system"), and the translation of types of §7.2.1 "Evidence" / §7.2.2 "Translating
types" (Figure 12a "Evidence passing").  The start and end of each part is marked by
`-- [PAPER ▶ START]` / `-- [PAPER ◀ END]` comments.

The core calculus is the qualified language without constraints: evidence is passed
explicitly.  As in the paper, it has linear pairs `τ₁ ⊗ τ₂`, the unit type `𝟏`, `Ur τ`,
polymorphic `let`-bindings (type schemes `∀ā. τ` in the context, instantiated at variables)
and existential pairs `∃ā. τ ⊗ υ` (`exPair`).  Type variables are de Bruijn indices, as in the
qualified language (`CTy P k`), and core expressions use de Bruijn indices too
(`CTm sig k n`).

**Evidence.**  The paper assumes a type `⟦q⟧` of evidence for each atomic constraint, extends
it to simple constraints by `⟦ε⟧ = 𝟏`, `⟦Q₁ ⊗ Q₂⟧ = ⟦Q₁⟧ ⊗ ⟦Q₂⟧`, …, and assumes a linear
function `⟦Q₁ ⊩ Q₂⟧ : ⟦Q₁⟧ ⊸ ⟦Q₂⟧` for each entailment.  Since simple constraints are
unordered (a footnote of §7.2.3 points out that this makes the splitting of evidence
ill-defined), we take the type `ev Q` of evidence for `Q` as primitive, together with the
following linear primitives, which are exactly the operations on evidence used by the
desugaring of the paper:
* `coe Q₁ Q₂ : ev Q₁ ⊸ ev Q₂` when `Q₁ ⊩ Q₂` (the paper's `⟦Q₁ ⊩ Q₂⟧`);
* `split Q₁ Q₂ : ev (Q₁ ⊗ Q₂) ⊸ ev Q₁ ⊗ ev Q₂` and `join Q₁ Q₂ : ev Q₁ ⊗ ev Q₂ ⊸ ev (Q₁ ⊗ Q₂)`;
* `drop : ev ε ⊸ 𝟏`;
* `urEv Q : ev (ω·Q) ⊸ Ur (ev (ω·Q))` (the paper's `⌊e⌋_Q`).

Since evidence types mention constraints of the qualified language, the type variables of core
types are instantiated with types of the qualified language (through their translation `⟦τ⟧`):
`CTy.subst` takes a substitution by qualified types.
-/

@[expose] public section

noncomputable section

namespace LQT

open SConstr

variable {P : Type}

-- [PAPER ▶ START] §7.1 › Figure 11 / Appendix A.1 › Figure 13 "Grammar of the core calculus": types
--   `τ, υ ::= a | ∃ā. τ ⊗ υ | τ₁ →_π τ₂ | T τ̄ | …` (`ev Q` is the evidence type `⟦Q⟧` of §7.2.1,
--   taken as primitive; see the file header)
/-- Types of the core calculus, with `k` type variables in scope. -/
inductive CTy (P : Type) : Nat → Type
  | tvar {k} : Fin k → CTy P k
  | arr {k} : Mult → CTy P k → CTy P k → CTy P k
  | tensor {k} : CTy P k → CTy P k → CTy P k
  | unit {k} : CTy P k
  | ur {k} : CTy P k → CTy P k
  | data {k} (T p : Nat) (args : Fin p → CTy P k) : CTy P k
  /-- The type `⟦Q⟧` of evidence for a simple constraint `Q`. -/
  | ev {k} : SConstr (Atom P k) → CTy P k
  /-- Existential pairs `∃ā. τ ⊗ υ`, binding `j` type variables. -/
  | exPair {k} (j : Nat) : CTy P (k + j) → CTy P (k + j) → CTy P k

-- [PAPER ◀ END] §7.1 › Figure 11 / Figure 13 (core types)

-- [PAPER ▶ START] §7.2.2 "Translating types": `⟦τ₁ →_π τ₂⟧ = ⟦τ₁⟧ →_π ⟦τ₂⟧`, `⟦∃ā. τ ⇐ Q⟧ = ∃ā. ⟦τ⟧
--   ⊗ ⟦Q⟧`, …
/-- Translation of types `⟦τ⟧` (§7.2.2): `⟦∃ā. τ ⇐ Q⟧ = ∃ā. ⟦τ⟧ ⊗ ⟦Q⟧`. -/
def Ty.ds : {k : Nat} → Ty P k → CTy P k
  | _, .tvar a => .tvar a
  | _, .arr π τ₁ τ₂ => .arr π τ₁.ds τ₂.ds
  | _, .exq j τ m mul pred ar args => .exPair j τ.ds (.ev (exqC m mul pred ar args))
  | _, .data T p args => .data T p (fun l => (args l).ds)

-- [PAPER ◀ END] §7.2.2, translation of types

-- [NOT IN PAPER ▶ START] renaming and substitution in core types, and their commutation with the
--   translation
/-- Renaming of type variables in core types. -/
def CTy.rename : {k k' : Nat} → (Fin k → Fin k') → CTy P k → CTy P k'
  | _, _, r, .tvar a => .tvar (r a)
  | _, _, r, .arr π τ₁ τ₂ => .arr π (τ₁.rename r) (τ₂.rename r)
  | _, _, r, .tensor τ₁ τ₂ => .tensor (τ₁.rename r) (τ₂.rename r)
  | _, _, _, .unit => .unit
  | _, _, r, .ur τ => .ur (τ.rename r)
  | _, _, r, .data T p args => .data T p (fun l => (args l).rename r)
  | _, _, r, .ev Q => .ev (Q.rename r)
  | _, _, r, .exPair j τ υ => .exPair j (τ.rename (liftRen j r)) (υ.rename (liftRen j r))

/-- Substitution of (translations of) qualified types for type variables in core types. -/
def CTy.subst : {k k' : Nat} → (Fin k → Ty P k') → CTy P k → CTy P k'
  | _, _, σ, .tvar a => (σ a).ds
  | _, _, σ, .arr π τ₁ τ₂ => .arr π (τ₁.subst σ) (τ₂.subst σ)
  | _, _, σ, .tensor τ₁ τ₂ => .tensor (τ₁.subst σ) (τ₂.subst σ)
  | _, _, _, .unit => .unit
  | _, _, σ, .ur τ => .ur (τ.subst σ)
  | _, _, σ, .data T p args => .data T p (fun l => (args l).subst σ)
  | _, _, σ, .ev Q => .ev (Q.tsubst σ)
  | _, _, σ, .exPair j τ υ => .exPair j (τ.subst (liftSub j σ)) (υ.subst (liftSub j σ))

/-- The translation of types commutes with renaming. -/
theorem Ty.ds_rename {k k' : Nat} (r : Fin k → Fin k') (τ : Ty P k) :
    (τ.rename r).ds = τ.ds.rename r := by
  induction τ generalizing k' with
  | tvar a => rfl
  | arr π τ₁ τ₂ ih₁ ih₂ => simp [Ty.rename, Ty.ds, CTy.rename, ih₁, ih₂]
  | exq j τ m mul pred ar args ih _ =>
    simp only [Ty.rename, Ty.ds, CTy.rename, ih, exqC_rename]
  | data T p args ih => simp [Ty.rename, Ty.ds, CTy.rename, ih]

/-- The translation of types commutes with substitution. -/
theorem Ty.ds_subst {k k' : Nat} (σ : Fin k → Ty P k') (τ : Ty P k) :
    (τ.subst σ).ds = τ.ds.subst σ := by
  induction τ generalizing k' with
  | tvar a => rfl
  | arr π τ₁ τ₂ ih₁ ih₂ => simp [Ty.subst, Ty.ds, CTy.subst, ih₁, ih₂]
  | exq j τ m mul pred ar args ih _ =>
    simp only [Ty.subst, Ty.ds, CTy.subst, ih, exqC_subst]
  | data T p args ih => simp [Ty.subst, Ty.ds, CTy.subst, ih]

/-! ### Identity substitutions -/

lemma liftRen_zero {k k' : Nat} (r : Fin k → Fin k') : liftRen 0 r = r := by
  funext a
  have : a = Fin.castAdd 0 a := Fin.ext rfl
  rw [this, liftRen, Fin.addCases_left]
  rfl

lemma liftSub_tvar {k j : Nat} : liftSub j (Ty.tvar : Fin k → Ty P k) = Ty.tvar := by
  funext a
  refine Fin.addCases (fun b => ?_) (fun b => ?_) a
  · simp [liftSub, Ty.rename]
  · simp [liftSub]

lemma Ty.subst_tvar {k : Nat} (τ : Ty P k) : τ.subst Ty.tvar = τ := by
  induction τ with
  | tvar a => rfl
  | arr π τ₁ τ₂ ih₁ ih₂ => simp [Ty.subst, ih₁, ih₂]
  | exq j τ m mul pred ar args ih iha =>
    simp only [Ty.subst, liftSub_tvar, ih, iha]
  | data T p args ih => simp [Ty.subst, ih]

lemma SConstr.tsubst_tvar {k : Nat} (Q : SConstr (Atom P k)) : Q.tsubst Ty.tvar = Q := by
  have h : ∀ q : Atom P k, Atom.subst Ty.tvar q = q := by
    intro q
    obtain ⟨p, ts⟩ := q
    show (p, ts.map (Ty.subst Ty.tvar)) = (p, ts)
    rw [show (Ty.subst Ty.tvar : Ty P k → Ty P k) = id from funext Ty.subst_tvar, List.map_id]
  unfold SConstr.tsubst
  rw [map_congr h, map_id']

lemma CTy.subst_tvar {k : Nat} (τ : CTy P k) : τ.subst Ty.tvar = τ := by
  induction τ with
  | tvar a => rfl
  | arr π τ₁ τ₂ ih₁ ih₂ => simp [CTy.subst, ih₁, ih₂]
  | tensor τ₁ τ₂ ih₁ ih₂ => simp [CTy.subst, ih₁, ih₂]
  | unit => rfl
  | ur τ ih => simp [CTy.subst, ih]
  | data T p args ih => simp [CTy.subst, ih]
  | ev Q => simp [CTy.subst, SConstr.tsubst_tvar]
  | exPair j τ υ ih₁ ih₂ => simp only [CTy.subst, liftSub_tvar, ih₁, ih₂]

lemma instSub_zero {k : Nat} (τs : Fin 0 → Ty P k) : instSub τs = Ty.tvar := by
  funext a
  have : a = Fin.castAdd 0 a := Fin.ext rfl
  rw [this, instSub, Fin.addCases_left]
  rfl

-- [NOT IN PAPER ◀ END] renaming and substitution in core types

/-! ### Core type schemes and contexts -/

-- [PAPER ▶ START] §7.1 › Figure 11 / Figure 13: type schemes `σ ::= ∀ā. τ`
/-- Core type schemes `∀ā. τ`. -/
structure CScheme (P : Type) (k : Nat) where
  /-- The number of quantified type variables. -/
  j : Nat
  /-- The type. -/
  τ : CTy P (k + j)

-- [PAPER ◀ END] §7.1 › Figure 11 / Figure 13 (type schemes)

-- [NOT IN PAPER ▶ START] helpers on core schemes and contexts
/-- A core type seen as a scheme without quantified variables. -/
def CScheme.mono {k : Nat} (τ : CTy P k) : CScheme P k := ⟨0, τ⟩

/-- Renaming of the free type variables of a core type scheme. -/
def CScheme.rename {k k' : Nat} (r : Fin k → Fin k') (σ : CScheme P k) : CScheme P k' :=
  ⟨σ.j, σ.τ.rename (liftRen σ.j r)⟩

@[simp] lemma CScheme.rename_mono {k k' : Nat} (r : Fin k → Fin k') (τ : CTy P k) :
    (CScheme.mono τ).rename r = CScheme.mono (τ.rename r) := by
  simp [CScheme.rename, CScheme.mono, liftRen_zero]

/-- Weakening of a core context by `j` new type variables. -/
def cctxWk {k n : Nat} (j : Nat) (Γ : Fin n → CScheme P k) : Fin n → CScheme P (k + j) :=
  fun x => (Γ x).rename (Fin.castAdd j)

-- [NOT IN PAPER ◀ END] helpers on core schemes and contexts

-- [PAPER ▶ START] §7.2.2 "Translating types": `⟦∀ā. Q ⇒ τ⟧ = ∀ā. ⟦Q⟧ ⊸ ⟦τ⟧`
/-- Translation of type schemes: `⟦∀ā. Q ⇒ τ⟧ = ∀ā. ⟦Q⟧ →₁ ⟦τ⟧`, and `⟦∀ā. ε ⇒ τ⟧ = ∀ā. ⟦τ⟧`
(so that unqualified types are translated as in the paper's translation of contexts). -/
def Scheme.ds {k : Nat} (σ : Scheme P k) : CScheme P k :=
  ⟨σ.j, if σ.Q = 0 then σ.τ.ds else .arr .one (.ev σ.Q) σ.τ.ds⟩

-- [PAPER ◀ END] §7.2.2, translation of type schemes

-- [NOT IN PAPER ▶ START] properties of the translation of schemes
@[simp] lemma Scheme.ds_mono {k : Nat} (τ : Ty P k) : (Scheme.mono τ).ds = CScheme.mono τ.ds := by
  simp [Scheme.ds, Scheme.mono, CScheme.mono]

/-- The translation of schemes commutes with renaming. -/
theorem Scheme.ds_rename {k k' : Nat} (r : Fin k → Fin k') (σ : Scheme P k) :
    (σ.rename r).ds = σ.ds.rename r := by
  simp only [Scheme.ds, Scheme.rename, CScheme.rename, SConstr.rename, SConstr.map_eq_zero_iff]
  congr 1
  split_ifs <;> simp [Ty.ds_rename, CTy.rename, SConstr.rename]

-- [NOT IN PAPER ◀ END] properties of the translation of schemes

-- [PAPER ▶ START] §7.2.1 "Evidence": the function `⟦Q₁ ⊩ Q₂⟧ : ⟦Q₁⟧ ⊸ ⟦Q₂⟧` is `coe`;
--   `split`/`join`/`drop`/`urEv` replace the equations of Figure 12a "Evidence passing" (`⟦ε⟧ = 𝟏`,
--   `⟦Q₁ ⊗ Q₂⟧ = ⟦Q₁⟧ ⊗ ⟦Q₂⟧`, `⟦ω·q⟧ = Ur ⟦q⟧`), see the file header
/-! ### Evidence primitives -/

/-- Primitive operations on evidence. -/
inductive Prim (P : Type) (k : Nat)
  | coe : SConstr (Atom P k) → SConstr (Atom P k) → Prim P k
  | split : SConstr (Atom P k) → SConstr (Atom P k) → Prim P k
  | join : SConstr (Atom P k) → SConstr (Atom P k) → Prim P k
  | drop : Prim P k
  | urEv : SConstr (Atom P k) → Prim P k

/-- Typing of the evidence primitives: `PrimTy D p τ₁ τ₂` means `p : τ₁ ⊸ τ₂`. -/
inductive PrimTy {k : Nat} (D : Domain (Atom P k)) : Prim P k → CTy P k → CTy P k → Prop
  | coe {Q₁ Q₂} : D.Entails Q₁ Q₂ → PrimTy D (.coe Q₁ Q₂) (.ev Q₁) (.ev Q₂)
  | split (Q₁ Q₂) : PrimTy D (.split Q₁ Q₂) (.ev (Q₁ + Q₂)) (.tensor (.ev Q₁) (.ev Q₂))
  | join (Q₁ Q₂) : PrimTy D (.join Q₁ Q₂) (.tensor (.ev Q₁) (.ev Q₂)) (.ev (Q₁ + Q₂))
  | drop : PrimTy D .drop (.ev 0) .unit
  | urEv (Q) : PrimTy D (.urEv Q) (.ev ((Mult.omega : Mult) • Q))
      (.ur (.ev ((Mult.omega : Mult) • Q)))

-- [PAPER ◀ END] §7.2.1 / Figure 12a (evidence)

/-! ### Core expressions and their typing -/

-- [PAPER ▶ START] §7.1 › Figure 11 / Appendix A.1 › Figure 13: core expressions (with explicit
--   pairs, unit, `Ur` and the evidence primitives)
/-- Expressions of the core calculus with `k` type variables and `n` expression variables in
scope (de Bruijn indices). -/
inductive CTm (sig : DataSig P) : Nat → Nat → Type
  | var {k n} : Fin n → CTm sig k n
  | con {k n} (T : Nat) (i : Fin (sig.ncons T)) : CTm sig k n
  | lam {k n} : CTm sig k (n + 1) → CTm sig k n
  | app {k n} : CTm sig k n → CTm sig k n → CTm sig k n
  /-- Linear pairs `(e₁, e₂)`. -/
  | pair {k n} : CTm sig k n → CTm sig k n → CTm sig k n
  /-- `case e of (x, y) → e'`: `x` is bound at index `0` and `y` at index `1`. -/
  | letPair {k n} : CTm sig k n → CTm sig k (n + 2) → CTm sig k n
  /-- The unit value `()`. -/
  | unit {k n} : CTm sig k n
  /-- `case e of () → e'`. -/
  | letUnit {k n} : CTm sig k n → CTm sig k n → CTm sig k n
  /-- `Ur e`. -/
  | urI {k n} : CTm sig k n → CTm sig k n
  /-- `case e of Ur x → e'`. -/
  | letUr {k n} : CTm sig k n → CTm sig k (n + 1) → CTm sig k n
  /-- `let_π x = e₁ in e₂` (monomorphic). -/
  | let_ {k n} : Mult → CTm sig k n → CTm sig k (n + 1) → CTm sig k n
  /-- `let_π x : ∀ā. τ = e₁ in e₂`, generalising `j` type variables of `e₁`. -/
  | letGen {k n} : Mult → (j : Nat) → CTm sig (k + j) n → CTm sig k (n + 1) → CTm sig k n
  /-- `case_π e of { Kᵢ x̄ᵢ → eᵢ }`. -/
  | case {k n} : Mult → CTm sig k n → (T : Nat) →
      ((i : Fin (sig.ncons T)) → CTm sig k (sig.arity T i + n)) → CTm sig k n
  /-- Application of an evidence primitive. -/
  | prim {k n} : Prim P k → CTm sig k n → CTm sig k n
  /-- Existential pairs `pack (e₁, e₂)`. -/
  | pack {k n} : CTm sig k n → CTm sig k n → CTm sig k n
  /-- `let pack (x, y) = e₁ in e₂`, opening `j` type variables in `e₂`; `x` is bound at index
  `0` and `y` at index `1`. -/
  | unpack {k n} (j : Nat) : CTm sig k n → CTm sig (k + j) (n + 2) → CTm sig k n

-- [PAPER ◀ END] §7.1 › Figure 11 / Figure 13 (core expressions)

-- [PAPER ▶ START] Appendix A.1 › Figure 14, rule L_Case: the context of the branches
/-- The context of a core `case` alternative. -/
def caseCtxC (sig : DataSig P) {k n : Nat} (Γ : Fin n → CScheme P k) (T : Nat)
    (i : Fin (sig.ncons T)) (τs : Fin (sig.params T) → Ty P k) :
    Fin (sig.arity T i + n) → CScheme P k :=
  Fin.append (fun l => CScheme.mono ((sig.field T i l).2.subst τs).ds) Γ

-- [PAPER ◀ END] Appendix A.1 › Figure 14, context of rule L_Case

-- [PAPER ▶ START] §7.1 › Figure 11 / Appendix A.1 › Figure 14 "Core calculus type system": rules
--   L_Var, L_Abs, L_App, L_Pack, L_Unpack, L_Let, L_Case, plus the standard rules for pairs, unit,
--   `Ur`, polymorphic `let` and the evidence primitives, which the paper uses without listing them
/-- The typing judgement `Γ ⊢ e : τ` of the core calculus (Figure 11 / Appendix A.1, Figure 14). -/
inductive CHasType (D : LDomain (Atom P)) (sig : DataSig P) :
    {k n : Nat} → (Fin n → CScheme P k) → (Fin n → Usage) → CTm sig k n → CTy P k → Prop
  | var {k n} {Γ : Fin n → CScheme P k} {x : Fin n} {σ : CScheme P k} (v : Fin n → Usage)
      (τs : Fin σ.j → Ty P k) : Γ x = σ →
      CHasType D sig Γ (single x + (Mult.omega : Mult) • v) (.var x) (σ.τ.subst (instSub τs))
  | con {k n} {Γ : Fin n → CScheme P k} (v : Fin n → Usage) (T : Nat) (i : Fin (sig.ncons T))
      (τs : Fin (sig.params T) → Ty P k) :
      CHasType D sig Γ ((Mult.omega : Mult) • v) (.con T i) ((sig.conTy T i).subst τs).ds
  | lam {k n} {Γ : Fin n → CScheme P k} {u : Fin n → Usage} {π : Mult} {τ₁ τ₂ : CTy P k}
      {e : CTm sig k (n + 1)} :
      CHasType D sig (Fin.cons (CScheme.mono τ₁) Γ) (Fin.cons (Usage.ofMult π) u) e τ₂ →
      CHasType D sig Γ u (.lam e) (.arr π τ₁ τ₂)
  | app {k n} {Γ : Fin n → CScheme P k} {u₁ u₂ : Fin n → Usage} {π : Mult} {τ₁ τ : CTy P k}
      {e₁ e₂ : CTm sig k n} :
      CHasType D sig Γ u₁ e₁ (.arr π τ₁ τ) → CHasType D sig Γ u₂ e₂ τ₁ →
      CHasType D sig Γ (u₁ + π • u₂) (.app e₁ e₂) τ
  | pair {k n} {Γ : Fin n → CScheme P k} {u₁ u₂ : Fin n → Usage} {τ₁ τ₂ : CTy P k}
      {e₁ e₂ : CTm sig k n} :
      CHasType D sig Γ u₁ e₁ τ₁ → CHasType D sig Γ u₂ e₂ τ₂ →
      CHasType D sig Γ (u₁ + u₂) (.pair e₁ e₂) (.tensor τ₁ τ₂)
  | letPair {k n} {Γ : Fin n → CScheme P k} {u₁ u₂ : Fin n → Usage} {τ₁ τ₂ τ : CTy P k}
      {e₁ : CTm sig k n} {e₂ : CTm sig k (n + 2)} :
      CHasType D sig Γ u₁ e₁ (.tensor τ₁ τ₂) →
      CHasType D sig (Fin.cons (CScheme.mono τ₁) (Fin.cons (CScheme.mono τ₂) Γ))
        (Fin.cons Usage.one (Fin.cons Usage.one u₂)) e₂ τ →
      CHasType D sig Γ (u₁ + u₂) (.letPair e₁ e₂) τ
  | unit {k n} {Γ : Fin n → CScheme P k} (v : Fin n → Usage) :
      CHasType D sig Γ ((Mult.omega : Mult) • v) .unit .unit
  | letUnit {k n} {Γ : Fin n → CScheme P k} {u₁ u₂ : Fin n → Usage} {τ : CTy P k}
      {e₁ e₂ : CTm sig k n} :
      CHasType D sig Γ u₁ e₁ .unit → CHasType D sig Γ u₂ e₂ τ →
      CHasType D sig Γ (u₁ + u₂) (.letUnit e₁ e₂) τ
  | urI {k n} {Γ : Fin n → CScheme P k} {u : Fin n → Usage} {τ : CTy P k} {e : CTm sig k n} :
      CHasType D sig Γ u e τ → CHasType D sig Γ ((Mult.omega : Mult) • u) (.urI e) (.ur τ)
  | letUr {k n} {Γ : Fin n → CScheme P k} {u₁ u₂ : Fin n → Usage} {τ₁ τ : CTy P k}
      {e₁ : CTm sig k n} {e₂ : CTm sig k (n + 1)} :
      CHasType D sig Γ u₁ e₁ (.ur τ₁) →
      CHasType D sig (Fin.cons (CScheme.mono τ₁) Γ) (Fin.cons Usage.omega u₂) e₂ τ →
      CHasType D sig Γ (u₁ + u₂) (.letUr e₁ e₂) τ
  | let_ {k n} {Γ : Fin n → CScheme P k} {u₁ u₂ : Fin n → Usage} {π : Mult} {τ₁ τ : CTy P k}
      {e₁ : CTm sig k n} {e₂ : CTm sig k (n + 1)} :
      CHasType D sig Γ u₁ e₁ τ₁ →
      CHasType D sig (Fin.cons (CScheme.mono τ₁) Γ) (Fin.cons (Usage.ofMult π) u₂) e₂ τ →
      CHasType D sig Γ (π • u₁ + u₂) (.let_ π e₁ e₂) τ
  | letGen {k n j} {Γ : Fin n → CScheme P k} {u₁ u₂ : Fin n → Usage} {π : Mult}
      {τ₁ : CTy P (k + j)} {τ : CTy P k} {e₁ : CTm sig (k + j) n} {e₂ : CTm sig k (n + 1)} :
      CHasType D sig (cctxWk j Γ) u₁ e₁ τ₁ →
      CHasType D sig (Fin.cons ⟨j, τ₁⟩ Γ) (Fin.cons (Usage.ofMult π) u₂) e₂ τ →
      CHasType D sig Γ (π • u₁ + u₂) (.letGen π j e₁ e₂) τ
  | case {k n} {Γ : Fin n → CScheme P k} {u₁ u₂ : Fin n → Usage} {π : Mult} {τ : CTy P k}
      {e : CTm sig k n} {T : Nat} {τs : Fin (sig.params T) → Ty P k}
      {alts : (i : Fin (sig.ncons T)) → CTm sig k (sig.arity T i + n)} :
      CHasType D sig Γ u₁ e (.data T (sig.params T) (fun l => (τs l).ds)) →
      (∀ i, CHasType D sig (caseCtxC sig Γ T i τs) (caseUsage sig π u₂ T i) (alts i) τ) →
      CHasType D sig Γ (π • u₁ + u₂) (.case π e T alts) τ
  | prim {k n} {Γ : Fin n → CScheme P k} {u : Fin n → Usage} {p : Prim P k} {τ₁ τ₂ : CTy P k}
      {e : CTm sig k n} :
      PrimTy (D k) p τ₁ τ₂ → CHasType D sig Γ u e τ₁ → CHasType D sig Γ u (.prim p e) τ₂
  | pack {k n j} {Γ : Fin n → CScheme P k} {u₁ u₂ : Fin n → Usage} {τ υ : CTy P (k + j)}
      {e₁ e₂ : CTm sig k n} (υs : Fin j → Ty P k) :
      CHasType D sig Γ u₁ e₁ (τ.subst (instSub υs)) →
      CHasType D sig Γ u₂ e₂ (υ.subst (instSub υs)) →
      CHasType D sig Γ (u₁ + u₂) (.pack e₁ e₂) (.exPair j τ υ)
  | unpack {k n j} {Γ : Fin n → CScheme P k} {u₁ u₂ : Fin n → Usage} {τ₁ υ₁ : CTy P (k + j)}
      {τ : CTy P k} {e₁ : CTm sig k n} {e₂ : CTm sig (k + j) (n + 2)} :
      CHasType D sig Γ u₁ e₁ (.exPair j τ₁ υ₁) →
      CHasType D sig (Fin.cons (CScheme.mono τ₁) (Fin.cons (CScheme.mono υ₁) (cctxWk j Γ)))
        (Fin.cons Usage.one (Fin.cons Usage.one u₂)) e₂ (τ.rename (Fin.castAdd j)) →
      CHasType D sig Γ (u₁ + u₂) (.unpack j e₁ e₂) τ

-- [PAPER ◀ END] §7.1 › Figure 11 / Figure 14

-- [NOT IN PAPER ▶ START] helpers on core typing
/-- Rewriting the usage vector and the type of a core typing judgement along equalities. -/
lemma CHasType.cast {D : LDomain (Atom P)} {sig : DataSig P} {k n : Nat}
    {Γ : Fin n → CScheme P k} {u u' : Fin n → Usage} {e : CTm sig k n} {τ τ' : CTy P k}
    (h : CHasType D sig Γ u e τ) (hu : u = u') (hτ : τ = τ') : CHasType D sig Γ u' e τ' :=
  hu ▸ hτ ▸ h

/-- Variables bound to a monomorphic type. -/
lemma CHasType.var_mono {D : LDomain (Atom P)} {sig : DataSig P} {k n : Nat}
    {Γ : Fin n → CScheme P k} {x : Fin n} {τ : CTy P k} (v : Fin n → Usage)
    (hx : Γ x = CScheme.mono τ) :
    CHasType D sig Γ (single x + (Mult.omega : Mult) • v) (.var x) τ :=
  (CHasType.var (σ := CScheme.mono τ) v Fin.elim0 hx).cast rfl
    (by simp [CScheme.mono, instSub_zero, CTy.subst_tvar])

-- [NOT IN PAPER ◀ END] helpers on core typing

end LQT
