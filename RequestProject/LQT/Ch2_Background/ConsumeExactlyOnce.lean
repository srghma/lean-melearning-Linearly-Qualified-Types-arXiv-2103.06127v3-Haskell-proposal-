module

public import RequestProject.LQT.Ch7_Desugaring.CoreCalculus
public import RequestProject.LQT.Infrastructure.UsageVec

/-!
# "Consume exactly once" (§2, Definition 2.1)

Paper location: §2 "Background: Linear Haskell", Definition 2.1 "Consume exactly once", and the
meaning of the linear arrow quoted just before it ("`f :: a ⊸ b` guarantees that if `(f u)` is
consumed exactly once, then the argument `u` is consumed exactly once").

Definition 2.1 describes how a value is *consumed* at run time:

* to consume a value of atomic base type exactly once, just evaluate it;
* to consume a function exactly once, apply it to one argument, and then consume its result
  exactly once;
* to consume a pair exactly once, pattern-match on it, and then consume each component exactly
  once;
* in general, to consume a value of an algebraic datatype exactly once, pattern-match on it,
  and then consume all its linear components exactly once.

The paper gives no operational semantics, so we cannot state the run-time property itself.
What we formalize is the *syntactic* reading of the definition: `Consumes Γ x τ e` says that the
program `e` (of the core calculus of §7, which has exactly the type formers the definition talks
about: the atomic type `𝟏`, functions `τ₁ →_π τ₂`, linear pairs `τ₁ ⊗ τ₂` and the data type
`Ur τ`, whose single component is not linear) consumes the variable `x : τ` exactly once,
following the four clauses above.  We prove

* `Consumes.typed`: such a consumer is well typed and uses `x` with multiplicity exactly `1`, and
  no other variable linearly (its usage vector is `single x`): consuming exactly once is a
  linear use;
* `linear_arrow_meaning`: if `f : τ₁ ⊸ τ₂` and the result of `f y` is consumed exactly once, then
  `y` is used exactly once (the static counterpart of the meaning of the linear arrow), whereas
  with `f : τ₁ → τ₂` the argument `y` gets multiplicity `ω` (`unrestricted_arrow_meaning`).

The atomic base type is represented by `𝟏` (evaluating a value of an atomic type is a pattern
match without fields), and `Ur τ` represents the general case of a data type with a
non-linear component.  Variables are de Bruijn indices: the consumer is a term in the same
context as the variable it consumes, and the variables bound by the pattern matches of the
consumer are in front of that context.
-/

@[expose] public section

namespace LQT

variable {P : Type} {D : LDomain (Atom P)} {sig : DataSig P}

-- [PAPER ▶ START] §2 › Definition 2.1 "Consume exactly once" (syntactic reading)

/-- `Consumes Γ x τ e`: the core program `e` consumes the variable `x`, of type `τ`, exactly once
(Definition 2.1), and returns `()`.  Arguments passed to functions are programs that use no
variable linearly (usage `0`). -/
inductive Consumes {k : Nat} : {n : Nat} → (Fin n → CScheme P k) → Fin n → CTy P k →
    CTm sig k n → Prop
  /-- A value of atomic base type is consumed by evaluating it: `case x of () → ()`. -/
  | base {n} {Γ : Fin n → CScheme P k} {x : Fin n} :
      Consumes Γ x .unit (.letUnit (.var x) .unit)
  /-- A function is consumed by applying it to one argument `a` and consuming the result
  exactly once: `let₁ y = x a in e`. -/
  | fn {n} {Γ : Fin n → CScheme P k} {x : Fin n} {π : Mult} {τ₁ τ₂ : CTy P k}
      {a : CTm sig k n} {e : CTm sig k (n + 1)} :
      CHasType D sig Γ 0 a τ₁ → Consumes (Fin.cons (CScheme.mono τ₂) Γ) 0 τ₂ e →
      Consumes Γ x (.arr π τ₁ τ₂) (.let_ .one (.app (.var x) a) e)
  /-- A pair is consumed by pattern-matching on it and consuming each component exactly once:
  `case x of (y₁, y₂) → case e₁ of () → e₂`. -/
  | pair {n} {Γ : Fin n → CScheme P k} {x : Fin n} {τ₁ τ₂ : CTy P k}
      {e₁ e₂ : CTm sig k (n + 2)} :
      Consumes (Fin.cons (CScheme.mono τ₁) (Fin.cons (CScheme.mono τ₂) Γ)) 0 τ₁ e₁ →
      Consumes (Fin.cons (CScheme.mono τ₁) (Fin.cons (CScheme.mono τ₂) Γ)) 1 τ₂ e₂ →
      Consumes Γ x (.tensor τ₁ τ₂) (.letPair (.var x) (.letUnit e₁ e₂))
  /-- A value of the data type `Ur τ` is consumed by pattern-matching on it; its component is
  not linear, so nothing more is required: `case x of Ur y → ()`. -/
  | ur {n} {Γ : Fin n → CScheme P k} {x : Fin n} {τ : CTy P k} :
      Consumes Γ x (.ur τ) (.letUr (.var x) .unit)

-- [PAPER ◀ END] §2 › Definition 2.1

-- [NOT IN PAPER ▶ START] the syntactic reading of Definition 2.1 is a linear use

/-- A consumer of `x` (Definition 2.1) is well typed, and uses `x` exactly once and no other
variable linearly: its usage vector is `single x`. -/
theorem Consumes.typed {k n : Nat} {Γ : Fin n → CScheme P k} {x : Fin n} {τ : CTy P k}
    {e : CTm sig k n} (h : Consumes (D := D) Γ x τ e) (hx : Γ x = CScheme.mono τ) :
    CHasType D sig Γ (single x) e .unit := by
  induction h with
  | base =>
    refine (CHasType.letUnit (CHasType.var_mono 0 hx) (CHasType.unit 0)).cast ?_ rfl
    simp
  | @fn n Γ x π τ₁ τ₂ a e ha he ih =>
    have happ := CHasType.app (CHasType.var_mono (D := D) (sig := sig) 0 hx) ha
    have hbody := ih rfl
    rw [single_zero_eq] at hbody
    refine (CHasType.let_ (π := .one) happ (u₂ := 0) ?_).cast ?_ rfl
    · simpa using hbody
    · funext i; simp
  | @pair n Γ x τ₁ τ₂ e₁ e₂ h₁ h₂ ih₁ ih₂ =>
    have hb₁ := ih₁ rfl
    have hb₂ := ih₂ rfl
    have hsum : (single 0 + single 1 : Fin (n + 2) → Usage) =
        Fin.cons Usage.one (Fin.cons Usage.one 0) := by
      rw [single_zero_eq, show (1 : Fin (n + 2)) = (0 : Fin (n + 1)).succ from rfl,
        single_succ_eq, single_zero_eq]
      funext i
      refine Fin.cases ?_ (fun j => ?_) i
      · simp
      · refine Fin.cases ?_ (fun l => ?_) j <;> simp
    refine (CHasType.letPair (u₂ := 0) (CHasType.var_mono 0 hx) ?_).cast ?_ rfl
    · exact (CHasType.letUnit hb₁ hb₂).cast hsum rfl
    · simp
  | ur =>
    refine (CHasType.letUr (u₂ := 0) (CHasType.var_mono 0 hx) ?_).cast ?_ rfl
    · refine (CHasType.unit (Fin.cons Usage.one 0)).cast ?_ rfl
      funext i
      refine Fin.cases ?_ (fun j => ?_) i <;> simp
    · simp

/-- **The meaning of the linear arrow** (§2, static reading): if `f : τ₁ ⊸ τ₂` and the result of
`f y` is consumed exactly once (`let₁ z = f y in c`, where `c` consumes `z`), then `y` is used
exactly once (and so is `f`). -/
theorem linear_arrow_meaning {k n : Nat} {Γ : Fin n → CScheme P k} {f y : Fin n}
    {τ₁ τ₂ : CTy P k} {c : CTm sig k (n + 1)}
    (hf : Γ f = CScheme.mono (.arr .one τ₁ τ₂)) (hy : Γ y = CScheme.mono τ₁)
    (hc : Consumes (D := D) (Fin.cons (CScheme.mono τ₂) Γ) 0 τ₂ c) :
    CHasType D sig Γ (single f + single y) (.let_ .one (.app (.var f) (.var y)) c) .unit := by
  have happ := CHasType.app (CHasType.var_mono (D := D) (sig := sig) 0 hf)
    (CHasType.var_mono 0 hy)
  have hbody := hc.typed rfl
  rw [single_zero_eq] at hbody
  refine (CHasType.let_ (π := .one) happ (u₂ := 0) ?_).cast ?_ rfl
  · simpa using hbody
  · funext i; simp

/-- With an unrestricted function `f : τ₁ → τ₂` instead, consuming `f y` exactly once uses `y`
with multiplicity `ω`. -/
theorem unrestricted_arrow_meaning {k n : Nat} {Γ : Fin n → CScheme P k} {f y : Fin n}
    {τ₁ τ₂ : CTy P k} {c : CTm sig k (n + 1)}
    (hf : Γ f = CScheme.mono (.arr .omega τ₁ τ₂)) (hy : Γ y = CScheme.mono τ₁)
    (hc : Consumes (D := D) (Fin.cons (CScheme.mono τ₂) Γ) 0 τ₂ c) :
    CHasType D sig Γ (single f + (Mult.omega : Mult) • single y)
      (.let_ .one (.app (.var f) (.var y)) c) .unit := by
  have happ := CHasType.app (CHasType.var_mono (D := D) (sig := sig) 0 hf)
    (CHasType.var_mono 0 hy)
  have hbody := hc.typed rfl
  rw [single_zero_eq] at hbody
  refine (CHasType.let_ (π := .one) happ (u₂ := 0) ?_).cast ?_ rfl
  · simpa using hbody
  · funext i; simp

/-- Example: a pair `(𝟏, Ur τ)` is consumed by `case x of (y₁, y₂) → case (case y₁ of () → ())
of () → case y₂ of Ur _ → ()`. -/
theorem consumes_pair_example {k n : Nat} {Γ : Fin n → CScheme P k} {x : Fin n} {τ : CTy P k} :
    Consumes (D := D) (sig := sig) Γ x (.tensor .unit (.ur τ))
      (.letPair (.var x) (.letUnit (.letUnit (.var 0) .unit) (.letUr (.var 1) .unit))) :=
  .pair .base .ur

-- [NOT IN PAPER ◀ END] the syntactic reading of Definition 2.1 is a linear use

end LQT
