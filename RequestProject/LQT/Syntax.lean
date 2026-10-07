module

public import RequestProject.LQT.Wanted

/-!
# Syntax of the qualified language (§5.2, Figure 5)

Paper location: §5.2 "Typing rules", Figure 5 "Grammar of the qualified type system", and
Definition 5.1 "Atomic constraints" (§5.1).  The start and end of each part is marked by
`-- [PAPER ▶ START]` / `-- [PAPER ◀ END]` comments.

**Type variables** are de Bruijn indices: `Ty P k` is the type of types with `k` type variables
in scope (so `Ty P 0` is the type of closed types).  The binders `∀ā` (in type schemes) and `∃ā`
(in existential types) bind a *block* of `j` type variables at once: inside the binder the
variables in scope are `Fin (k + j)`, the bound variables being the last `j` ones.

* types `τ ::= a | τ₁ →_π τ₂ | ∃ā. τ ⇐ Q | T τ̄`;
* type schemes `σ ::= ∀ā. Q ⇒ τ`;
* expressions, with **de Bruijn indices** for expression variables as well: `Tm sig k n` is the
  type of expressions with `k` type variables and `n` expression variables in scope, so
  `Tm sig 0 0` is the type of closed expressions.  Binders extend the context at index `0`; a
  `case` alternative for a constructor with `m` fields binds `m` variables, which occupy the
  indices `0, …, m-1` of its body.  Expressions only mention types in the signature of
  `let x : σ = e₁ in e₂`; the type variables `ā` of `σ` scope over `e₁`, and the existential
  type variables `ā` opened by `let pack x = e₁ in e₂` scope over `e₂` (the number of opened
  variables is recorded in the syntax).

**Atomic constraints.**  An atomic constraint is a predicate symbol (from the parameter set `P`)
applied to a list of types, as in `RW n` (`Atom P k`).  The constraint of an existential type
`∃ā. τ ⇐ Q` is stored as a finite family of scaled atoms (an inductive type cannot be nested
inside the quotient types used for simple constraints); `exqC` turns it into a simple
constraint.

Data types are described by a signature `sig : DataSig P`: data type `T` has `sig.params T`
type parameters and `sig.ncons T` constructors; constructor `i` has `sig.arity T i` fields, and
field `l` has multiplicity and type `sig.field T i l` (a type whose free type variables are the
parameters).  Data constructors are typed as unrestricted variables of type
`∀ā. υ₁ →_π₁ ⋯ →_πₘ T ā`, as in the paper.
-/

@[expose] public section

noncomputable section

namespace LQT

open SConstr

-- [PAPER ▶ START] §5.2 › Figure 5 "Grammar of the qualified type system": types `τ, υ ::= a | ∃ā. τ
--   ⇐ Q | τ₁ →_π τ₂ | T τ̄`
/-- Types with `k` type variables in scope.  `P` is the set of predicate symbols of atomic
constraints. -/
inductive Ty (P : Type) : Nat → Type
  /-- Type variables `a`. -/
  | tvar {k} : Fin k → Ty P k
  /-- Function types `τ₁ →_π τ₂`. -/
  | arr {k} : Mult → Ty P k → Ty P k → Ty P k
  /-- Existential types `∃ā. τ ⇐ Q`, binding `j` type variables in `τ` and `Q`.  The
  constraint `Q` is the tensor product of the scaled atoms `mul i · pred i (args i)`,
  for `i < m` (see `exqC`). -/
  | exq {k} (j : Nat) (τ : Ty P (k + j)) (m : Nat) (mul : Fin m → Mult) (pred : Fin m → P)
      (ar : Fin m → Nat) (args : (i : Fin m) → Fin (ar i) → Ty P (k + j)) : Ty P k
  /-- Data types `T τ̄`, with `p` type arguments. -/
  | data {k} (T : Nat) (p : Nat) (args : Fin p → Ty P k) : Ty P k

-- [PAPER ◀ END] §5.2 › Figure 5 (types)

-- [PAPER ▶ START] §5.1 › Definition 5.1 "Atomic constraints" (the paper keeps the set abstract;
--   here an atom is a predicate symbol applied to types)
/-- Atomic constraints `q`: a predicate symbol applied to types. -/
def Atom (P : Type) (k : Nat) : Type := P × List (Ty P k)

noncomputable instance (P : Type) (k : Nat) : DecidableEq (Atom P k) := Classical.decEq _

-- [PAPER ◀ END] §5.1 › Definition 5.1

variable {P : Type}

-- [NOT IN PAPER ▶ START] renaming and substitution of type variables (the paper uses named
--   variables and writes `τ[τ̄/ā]`, `Q[τ̄/ā]`), and `exqC`, which turns the constraint stored in an
--   existential type into a simple constraint
/-! ### Renaming and substitution of type variables -/

/-- Lifting a renaming of type variables under a binder of `j` type variables. -/
def liftRen {k k' : Nat} (j : Nat) (r : Fin k → Fin k') : Fin (k + j) → Fin (k' + j) :=
  Fin.addCases (fun a => Fin.castAdd j (r a)) (fun b => Fin.natAdd k' b)

/-- Renaming of type variables. -/
def Ty.rename : {k k' : Nat} → (Fin k → Fin k') → Ty P k → Ty P k'
  | _, _, r, .tvar a => .tvar (r a)
  | _, _, r, .arr π τ₁ τ₂ => .arr π (τ₁.rename r) (τ₂.rename r)
  | _, _, r, .exq j τ m mul pred ar args =>
      .exq j (τ.rename (liftRen j r)) m mul pred ar (fun i l => (args i l).rename (liftRen j r))
  | _, _, r, .data T p args => .data T p (fun l => (args l).rename r)

/-- Lifting a substitution of type variables under a binder of `j` type variables. -/
def liftSub {k k' : Nat} (j : Nat) (σ : Fin k → Ty P k') : Fin (k + j) → Ty P (k' + j) :=
  Fin.addCases (fun a => (σ a).rename (Fin.castAdd j)) (fun b => .tvar (Fin.natAdd k' b))

/-- Simultaneous substitution of types for type variables. -/
def Ty.subst : {k k' : Nat} → (Fin k → Ty P k') → Ty P k → Ty P k'
  | _, _, σ, .tvar a => σ a
  | _, _, σ, .arr π τ₁ τ₂ => .arr π (τ₁.subst σ) (τ₂.subst σ)
  | _, _, σ, .exq j τ m mul pred ar args =>
      .exq j (τ.subst (liftSub j σ)) m mul pred ar (fun i l => (args i l).subst (liftSub j σ))
  | _, _, σ, .data T p args => .data T p (fun l => (args l).subst σ)

/-- Weakening of a type by `j` new type variables. -/
def Ty.wk {k : Nat} (j : Nat) (τ : Ty P k) : Ty P (k + j) := τ.rename (Fin.castAdd j)

/-- Instantiation of the last `j` type variables by the types `τs`: the substitution
`[τ̄/ā]` of the paper. -/
def instSub {k j : Nat} (τs : Fin j → Ty P k) : Fin (k + j) → Ty P k :=
  Fin.addCases Ty.tvar τs

/-- Renaming of an atomic constraint. -/
def Atom.rename {k k' : Nat} (r : Fin k → Fin k') (q : Atom P k) : Atom P k' :=
  (q.1, q.2.map (Ty.rename r))

/-- Substitution in an atomic constraint. -/
def Atom.subst {k k' : Nat} (σ : Fin k → Ty P k') (q : Atom P k) : Atom P k' :=
  (q.1, q.2.map (Ty.subst σ))

instance : Weakening (Atom P) := ⟨fun j q => q.rename (Fin.castAdd j)⟩

lemma wk_atom_def {k : Nat} (j : Nat) (q : Atom P k) :
    Weakening.wk j q = q.rename (Fin.castAdd j) := rfl

/-- Substitution in a simple constraint: `Q[σ]`. -/
def SConstr.tsubst {k k' : Nat} (σ : Fin k → Ty P k') (Q : SConstr (Atom P k)) :
    SConstr (Atom P k') :=
  Q.map (Atom.subst σ)

/-- Renaming in a simple constraint. -/
def SConstr.rename {k k' : Nat} (r : Fin k → Fin k') (Q : SConstr (Atom P k)) :
    SConstr (Atom P k') :=
  Q.map (Atom.rename r)

lemma SConstr.wk_eq_rename {k : Nat} (j : Nat) (Q : SConstr (Atom P k)) :
    Q.wk j = Q.rename (Fin.castAdd j) := rfl

/-- The constraint `Q` of an existential type `∃ā. τ ⇐ Q`. -/
def exqC {k : Nat} (m : Nat) (mul : Fin m → Mult) (pred : Fin m → P) (ar : Fin m → Nat)
    (args : (i : Fin m) → Fin (ar i) → Ty P k) : SConstr (Atom P k) :=
  ∑ i, atom (mul i) ((pred i, List.ofFn (args i)) : Atom P k)

lemma exqC_rename {k k' : Nat} (r : Fin k → Fin k') (m : Nat) (mul : Fin m → Mult)
    (pred : Fin m → P) (ar : Fin m → Nat) (args : (i : Fin m) → Fin (ar i) → Ty P k) :
    exqC m mul pred ar (fun i l => (args i l).rename r) =
      (exqC m mul pred ar args).rename r := by
  simp only [exqC, SConstr.rename, SConstr.map_sum, map_atom]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  simp [Atom.rename, List.map_ofFn]
  rfl

lemma exqC_subst {k k' : Nat} (σ : Fin k → Ty P k') (m : Nat) (mul : Fin m → Mult)
    (pred : Fin m → P) (ar : Fin m → Nat) (args : (i : Fin m) → Fin (ar i) → Ty P k) :
    exqC m mul pred ar (fun i l => (args i l).subst σ) =
      (exqC m mul pred ar args).tsubst σ := by
  simp only [exqC, SConstr.tsubst, SConstr.map_sum, map_atom]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  simp [Atom.subst, List.map_ofFn]
  rfl

-- [NOT IN PAPER ◀ END] renaming and substitution

/-! ### Type schemes -/

-- [PAPER ▶ START] §5.2 › Figure 5: type schemes `σ ::= ∀ā. Q ⇒ τ`
/-- Type schemes `σ = ∀ā. Q ⇒ τ`, binding `j` type variables in `Q` and `τ`. -/
structure Scheme (P : Type) (k : Nat) where
  /-- The number of quantified type variables. -/
  j : Nat
  /-- The constraint `Q` that must be provided to use the variable. -/
  Q : SConstr (Atom P (k + j))
  /-- The type `τ`. -/
  τ : Ty P (k + j)

-- [PAPER ◀ END] §5.2 › Figure 5 (type schemes)

-- [NOT IN PAPER ▶ START] helpers on schemes and contexts; `ctxWk` implements the freshness side
--   conditions on `ā` of rules E_Unpack and E_LetSig (Figure 6)
/-- A (monomorphic, unqualified) type `τ` seen as the scheme `∀. ε ⇒ τ`. -/
def Scheme.mono {k : Nat} (τ : Ty P k) : Scheme P k := ⟨0, 0, τ⟩

/-- Renaming of the free type variables of a type scheme. -/
def Scheme.rename {k k' : Nat} (r : Fin k → Fin k') (σ : Scheme P k) : Scheme P k' :=
  ⟨σ.j, σ.Q.rename (liftRen σ.j r), σ.τ.rename (liftRen σ.j r)⟩

/-- Weakening of a context by `j` new type variables (the paper's freshness condition on
`ā` in rules E_Unpack and E_LetSig). -/
def ctxWk {k n : Nat} (j : Nat) (Γ : Fin n → Scheme P k) : Fin n → Scheme P (k + j) :=
  fun x => (Γ x).rename (Fin.castAdd j)

-- [NOT IN PAPER ◀ END] helpers on schemes and contexts

/-! ### Data types -/

-- [PAPER ▶ START] §5.2 › Figure 5: type constructors `T` and data constructors `K` (the paper
--   leaves the declarations of data types implicit; here they are given by a signature)
/-- Signatures of data types. -/
structure DataSig (P : Type) where
  /-- Number of type parameters of each data type. -/
  params : Nat → Nat
  /-- Number of constructors of each data type. -/
  ncons : Nat → Nat
  /-- Number of fields of each constructor. -/
  arity : (T : Nat) → Fin (ncons T) → Nat
  /-- Multiplicity and type of each field (the type parameters are the type variables). -/
  field : (T : Nat) → (i : Fin (ncons T)) → Fin (arity T i) → Mult × Ty P (params T)

/-- `arrows m f r = υ₁ →_π₁ ⋯ →_πₘ r` where `f l = (πₗ, υₗ)`. -/
def arrows {k : Nat} : (m : Nat) → (Fin m → Mult × Ty P k) → Ty P k → Ty P k
  | 0, _, r => r
  | m + 1, f, r => .arr (f 0).1 (f 0).2 (arrows m (fun l => f l.succ) r)

/-- The type `υ₁ →_π₁ ⋯ →_πₘ T ā` of constructor `i` of data type `T` (its type variables are
the parameters `ā` of `T`). -/
def DataSig.conTy (sig : DataSig P) (T : Nat) (i : Fin (sig.ncons T)) : Ty P (sig.params T) :=
  arrows (sig.arity T i) (sig.field T i) (.data T (sig.params T) Ty.tvar)

-- [PAPER ◀ END] §5.2 › Figure 5 (type and data constructors)

/-! ### Expressions -/

-- [PAPER ▶ START] §5.2 › Figure 5: expressions `e ::= x | K | λx.e | e₁ e₂ | pack e | let pack x =
--   e₁ in e₂ | case_π e of {…} | let_π x = e₁ in e₂ | let_π x : σ = e₁ in e₂`
/-- Expressions of the qualified language, with `k` type variables and `n` expression
variables in scope (de Bruijn indices). -/
inductive Tm (sig : DataSig P) : Nat → Nat → Type
  /-- Variables `x`. -/
  | var {k n} : Fin n → Tm sig k n
  /-- Data constructors `K`. -/
  | con {k n} (T : Nat) (i : Fin (sig.ncons T)) : Tm sig k n
  /-- Abstraction `λx. e`. -/
  | lam {k n} : Tm sig k (n + 1) → Tm sig k n
  /-- Application `e₁ e₂`. -/
  | app {k n} : Tm sig k n → Tm sig k n → Tm sig k n
  /-- Packing `pack e`. -/
  | pack {k n} : Tm sig k n → Tm sig k n
  /-- Unpacking `let pack x = e₁ in e₂`, opening `j` existential type variables in `e₂`. -/
  | unpack {k n} (j : Nat) : Tm sig k n → Tm sig (k + j) (n + 1) → Tm sig k n
  /-- Let-binding `let_π x = e₁ in e₂`. -/
  | let_ {k n} : Mult → Tm sig k n → Tm sig k (n + 1) → Tm sig k n
  /-- Let-binding with a signature `let_π x : σ = e₁ in e₂` (the type variables of `σ` scope
  over `e₁`). -/
  | letSig {k n} : Mult → (σ : Scheme P k) → Tm sig (k + σ.j) n → Tm sig k (n + 1) → Tm sig k n
  /-- Case expression `case_π e of { Kᵢ x̄ᵢ → eᵢ }` on a value of data type `T`. -/
  | case {k n} : Mult → Tm sig k n → (T : Nat) →
      ((i : Fin (sig.ncons T)) → Tm sig k (sig.arity T i + n)) → Tm sig k n

-- [PAPER ◀ END] §5.2 › Figure 5 (expressions)

-- [PAPER ▶ START] §5.2 › Figure 6 "Qualified type system", rule E_Case: the context and usages of
--   the branches (premises of E_Case)
/-- The context of the `case` alternative for constructor `i` of `T τ̄`: the fields (with their
types `υᵢ[τ̄/ā]`) in front of `Γ`. -/
def caseCtx (sig : DataSig P) {k n : Nat} (Γ : Fin n → Scheme P k) (T : Nat)
    (i : Fin (sig.ncons T)) (τs : Fin (sig.params T) → Ty P k) :
    Fin (sig.arity T i + n) → Scheme P k :=
  Fin.append (fun l => Scheme.mono ((sig.field T i l).2.subst τs)) Γ

/-- The usage vector of the `case` alternative for constructor `i` of `T`, scrutinised with
multiplicity `π`: field `l` has usage `π ⋅ πₗ`. -/
def caseUsage (sig : DataSig P) {n : Nat} (π : Mult) (u : Fin n → Usage) (T : Nat)
    (i : Fin (sig.ncons T)) : Fin (sig.arity T i + n) → Usage :=
  Fin.append (fun l => Usage.ofMult (π * (sig.field T i l).1)) u

-- [PAPER ◀ END] §5.2 › Figure 6, premises of rule E_Case

end LQT
