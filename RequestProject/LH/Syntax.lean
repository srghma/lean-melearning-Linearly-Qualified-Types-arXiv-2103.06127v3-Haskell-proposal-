module

public import RequestProject.LH.Multiplicity

/-!
# Syntax of `λq→` (Linear Haskell, §3.1 Figure 5)

* `Ty Dn np m` : types `A, B ::= A →_π B | ∀p. A | D π₁ … πₙ` with `m` multiplicity
  variables in scope (`∀p` binds the multiplicity variable of index `0`).  `Dn` is the set of
  datatype names and `np d` is the number of multiplicity parameters of `d`.
* `Sig` : datatype declarations
  `data D p₁ … pₙ where (c_k : A₁ →_{μ₁} ⋯ A_{n_k} →_{μ_{n_k}} D)_{k=1..m}`:
  constructor `k` of `d` has `arity d k` fields; field `i` has type `fieldTy d k i` and
  multiplicity `fieldMult d k i`, whose multiplicity variables are the parameters `p₁ … pₙ`.
* `Tm S m n` : terms with `m` multiplicity variables and `n` term variables in scope, with
  **de Bruijn indices** for both.  `Tm S m 0` holds the terms without free term variables and
  `Tm S 0 0` the closed terms.  `λ_π (x : A). t` binds the term variable `0`; a `case`
  alternative for a constructor with `j` fields, and a `let` with `j` bindings, bind `j`
  variables, which are the *last* `j` indices `n, …, n + j - 1` of the body (in order).
* renaming (`Tm.rename`), substitution of terms for term variables (`Tm.subst`) and of
  multiplicities for multiplicity variables (`Tm.msubst`, `Ty.subst`).
-/

@[expose] public section

namespace LH

-- [PAPER ▶ START] §3.1 › Figure 5 "Syntax of λq→": types `A, B ::= A →_π B | ∀p. A | D p₁ … pₙ`
/-- Types of `λq→` with `m` multiplicity variables in scope. -/
inductive Ty (Dn : Type) (np : Dn → Nat) : Nat → Type
  /-- `A →_π B` -/
  | arr {m} : Ty Dn np m → Mult m → Ty Dn np m → Ty Dn np m
  /-- `∀p. A` (binds the multiplicity variable `0` of `A`) -/
  | all {m} : Ty Dn np (m + 1) → Ty Dn np m
  /-- `D π₁ … πₙ` -/
  | data {m} (d : Dn) (args : Fin (np d) → Mult m) : Ty Dn np m
-- [PAPER ◀ END] §3.1 › Figure 5 (types)

namespace Ty

variable {Dn : Type} {np : Dn → Nat}

-- [NOT IN PAPER ▶ START] substitution of multiplicities in types (the paper's `A[π/p]` and
--   `π[π₁ … πₙ]`)
/-- Substitution of multiplicities for the multiplicity variables of a type. -/
def subst : {m m' : Nat} → (Fin m → Mult m') → Ty Dn np m → Ty Dn np m'
  | _, _, s, arr A π B => arr (A.subst s) (π.subst s) (B.subst s)
  | _, _, s, all A => all (A.subst (Mult.liftS s))
  | _, _, s, data d args => data d (fun i => (args i).subst s)

/-- Weakening of a type (a new multiplicity variable of index `0`). -/
def wk {m : Nat} (A : Ty Dn np m) : Ty Dn np (m + 1) := A.subst (fun i => Mult.var i.succ)

theorem liftS_comp {m m' m'' : Nat} (s : Fin m → Mult m') (s' : Fin m' → Mult m'') :
    (fun i => (Mult.liftS s i).subst (Mult.liftS s')) =
      Mult.liftS (fun i => (s i).subst s') := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · rfl
  · simp only [Mult.liftS, Fin.cons_succ]
    exact Mult.subst_liftS_wk _ _

theorem subst_subst {m m' m'' : Nat} (s : Fin m → Mult m') (s' : Fin m' → Mult m'')
    (A : Ty Dn np m) : (A.subst s).subst s' = A.subst (fun i => (s i).subst s') := by
  induction A generalizing m' m'' with
  | arr A π B ihA ihB => simp only [subst, ihA, ihB, Mult.subst_subst]
  | all A ih => simp only [subst, ih, liftS_comp]
  | data d args => simp only [subst, Mult.subst_subst]

theorem liftS_var {m : Nat} : Mult.liftS (Mult.var : Fin m → Mult m) = Mult.var := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · rfl
  · rfl

theorem subst_var {m : Nat} (A : Ty Dn np m) : A.subst Mult.var = A := by
  induction A with
  | arr A π B ihA ihB => simp only [subst, ihA, ihB, Mult.subst_var_id]
  | all A ih => simp only [subst, liftS_var, ih]
  | data d args => simp only [subst, Mult.subst_var_id]

theorem subst_liftS_wk {m m' : Nat} (s : Fin m → Mult m') (A : Ty Dn np m) :
    (A.wk).subst (Mult.liftS s) = (A.subst s).wk := by
  unfold wk
  rw [subst_subst, subst_subst]
  rfl

theorem subst_cons_wk {m : Nat} (π : Mult m) (A : Ty Dn np m) :
    (A.wk).subst (Fin.cons π Mult.var) = A := by
  unfold wk; rw [subst_subst]; exact subst_var A

/-- Commutation of instantiation `A[π/p]` with substitution. -/
theorem subst_inst {m m' : Nat} (s : Fin m → Mult m') (A : Ty Dn np (m + 1)) (π : Mult m) :
    (A.subst (Fin.cons π Mult.var)).subst s =
      (A.subst (Mult.liftS s)).subst (Fin.cons (π.subst s) Mult.var) := by
  rw [subst_subst, subst_subst]
  congr 1
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · rfl
  · simp only [Mult.liftS, Fin.cons_succ, Mult.subst_var]
    exact (Mult.subst_cons_wk _ _).symm

theorem data_inj {m : Nat} {d d' : Dn} {a : Fin (np d) → Mult m} {a' : Fin (np d') → Mult m}
    (h : (data d a : Ty Dn np m) = data d' a') : d = d' ∧ HEq a a' := by
  cases h; exact ⟨rfl, HEq.rfl⟩
-- [NOT IN PAPER ◀ END]

end Ty

-- [PAPER ▶ START] §3.1 › Figure 5: datatype declarations
--   `data D p₁ … pₙ where (c_k : A₁ →_{π₁} ⋯ A_{n_k} →_{π_{n_k}} D)_{k=1..m}`
/-- A signature: a set of datatype declarations. -/
structure Sig where
  /-- Datatype names. -/
  Dn : Type
  /-- Number of multiplicity parameters `p₁ … pₙ` of each datatype. -/
  np : Dn → Nat
  /-- Number of constructors of each datatype. -/
  ncons : Dn → Nat
  /-- Number of fields of each constructor. -/
  arity : (d : Dn) → Fin (ncons d) → Nat
  /-- Type of each field (its multiplicity variables are the parameters). -/
  fieldTy : (d : Dn) → (k : Fin (ncons d)) → Fin (arity d k) → Ty Dn np (np d)
  /-- Multiplicity of each field (its multiplicity variables are the parameters). -/
  fieldMult : (d : Dn) → (k : Fin (ncons d)) → Fin (arity d k) → Mult (np d)
-- [PAPER ◀ END] §3.1 › Figure 5 (datatype declarations)

/-- Types over the datatypes of a signature. -/
abbrev Sig.Ty (S : Sig) (m : Nat) : Type := LH.Ty S.Dn S.np m

-- [PAPER ▶ START] §3.1 › Figure 5: terms `e, s, t, u ::= x | λ_π (x:A).t | t s | λp.t | t π |
--   c t₁ … tₙ | case_π t of {c_k x₁ … x_{n_k} → u_k} | let_π x₁ : A₁ = t₁ … xₙ : Aₙ = tₙ in u`
/-- Terms of `λq→` with `m` multiplicity variables and `n` term variables in scope. -/
inductive Tm (S : Sig) : Nat → Nat → Type
  /-- variable `x` -/
  | var {m n} : Fin n → Tm S m n
  /-- abstraction `λ_π (x : A). t` -/
  | lam {m n} : Mult m → S.Ty m → Tm S m (n + 1) → Tm S m n
  /-- application `t s` -/
  | app {m n} : Tm S m n → Tm S m n → Tm S m n
  /-- multiplicity abstraction `λp. t` -/
  | mlam {m n} : Tm S (m + 1) n → Tm S m n
  /-- multiplicity application `t π` -/
  | mapp {m n} : Tm S m n → Mult m → Tm S m n
  /-- data construction `c_k t₁ … t_{n_k}` (constructor `k` of datatype `d`) -/
  | con {m n} (d : S.Dn) (k : Fin (S.ncons d)) (args : Fin (S.arity d k) → Tm S m n) : Tm S m n
  /-- `case_π t of {c_k x₁ … x_{n_k} → u_k}` (one alternative per constructor of `d`) -/
  | case {m n} (π : Mult m) (t : Tm S m n) (d : S.Dn)
      (brs : (k : Fin (S.ncons d)) → Tm S m (n + S.arity d k)) : Tm S m n
  /-- `let_π x₁ : A₁ = t₁ … x_j : A_j = t_j in u` (non-recursive) -/
  | lett {m n} (π : Mult m) (j : Nat) (tys : Fin j → S.Ty m) (rhs : Fin j → Tm S m n)
      (body : Tm S m (n + j)) : Tm S m n
-- [PAPER ◀ END] §3.1 › Figure 5 (terms)

-- [NOT IN PAPER ▶ START] de Bruijn infrastructure: renaming, substitution
/-- Lifting a renaming under one binder. -/
def liftR {n n' : Nat} (ρ : Fin n → Fin n') : Fin (n + 1) → Fin (n' + 1) :=
  Fin.cases 0 (fun i => (ρ i).succ)

/-- Lifting a renaming under a block of `j` binders (bound at the end). -/
def liftRN {n n' : Nat} (j : Nat) (ρ : Fin n → Fin n') : Fin (n + j) → Fin (n' + j) :=
  Fin.addCases (fun i => Fin.castAdd j (ρ i)) (fun i => Fin.natAdd n' i)

namespace Tm

variable {S : Sig}

/-- Renaming of term variables. -/
def rename : {m n n' : Nat} → (Fin n → Fin n') → Tm S m n → Tm S m n'
  | _, _, _, ρ, var x => var (ρ x)
  | _, _, _, ρ, lam π A t => lam π A (t.rename (liftR ρ))
  | _, _, _, ρ, app t s => app (t.rename ρ) (s.rename ρ)
  | _, _, _, ρ, mlam t => mlam (t.rename ρ)
  | _, _, _, ρ, mapp t π => mapp (t.rename ρ) π
  | _, _, _, ρ, con d k args => con d k (fun i => (args i).rename ρ)
  | _, _, _, ρ, case π t d brs => case π (t.rename ρ) d (fun k => (brs k).rename (liftRN _ ρ))
  | _, _, _, ρ, lett π j tys rhs body =>
      lett π j tys (fun i => (rhs i).rename ρ) (body.rename (liftRN j ρ))

/-- Substitution of multiplicities for multiplicity variables. -/
def msubst : {m m' n : Nat} → (Fin m → Mult m') → Tm S m n → Tm S m' n
  | _, _, _, _, var x => var x
  | _, _, _, s, lam π A t => lam (π.subst s) (A.subst s) (t.msubst s)
  | _, _, _, s, app t u => app (t.msubst s) (u.msubst s)
  | _, _, _, s, mlam t => mlam (t.msubst (Mult.liftS s))
  | _, _, _, s, mapp t π => mapp (t.msubst s) (π.subst s)
  | _, _, _, s, con d k args => con d k (fun i => (args i).msubst s)
  | _, _, _, s, case π t d brs => case (π.subst s) (t.msubst s) d (fun k => (brs k).msubst s)
  | _, _, _, s, lett π j tys rhs body =>
      lett (π.subst s) j (fun i => (tys i).subst s) (fun i => (rhs i).msubst s) (body.msubst s)

/-- Weakening of multiplicity variables in a term. -/
def mwk {m n : Nat} (t : Tm S m n) : Tm S (m + 1) n := t.msubst (fun i => Mult.var i.succ)

/-- Lifting a substitution under one binder. -/
def liftσ {m n n' : Nat} (σ : Fin n → Tm S m n') : Fin (n + 1) → Tm S m (n' + 1) :=
  Fin.cases (var 0) (fun i => (σ i).rename Fin.succ)

/-- Lifting a substitution under a block of `j` binders (bound at the end). -/
def liftσN {m n n' : Nat} (j : Nat) (σ : Fin n → Tm S m n') : Fin (n + j) → Tm S m (n' + j) :=
  Fin.addCases (fun i => (σ i).rename (Fin.castAdd j)) (fun i => var (Fin.natAdd n' i))

/-- Parallel substitution of terms for term variables. -/
def subst : {m n n' : Nat} → (Fin n → Tm S m n') → Tm S m n → Tm S m n'
  | _, _, _, σ, var x => σ x
  | _, _, _, σ, lam π A t => lam π A (t.subst (liftσ σ))
  | _, _, _, σ, app t s => app (t.subst σ) (s.subst σ)
  | _, _, _, σ, mlam t => mlam (t.subst (fun i => (σ i).mwk))
  | _, _, _, σ, mapp t π => mapp (t.subst σ) π
  | _, _, _, σ, con d k args => con d k (fun i => (args i).subst σ)
  | _, _, _, σ, case π t d brs => case π (t.subst σ) d (fun k => (brs k).subst (liftσN _ σ))
  | _, _, _, σ, lett π j tys rhs body =>
      lett π j tys (fun i => (rhs i).subst σ) (body.subst (liftσN j σ))

end Tm
-- [NOT IN PAPER ◀ END]

end LH
