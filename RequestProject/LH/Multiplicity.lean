module

public import Mathlib

/-!
# Multiplicities of `λq→` (Linear Haskell, §3.1 Figure 5 and §3.2 Definition 3.4)

Paper: *Linear Haskell — Practical Linearity in a Higher-Order Polymorphic Language*
(`hlt.typ`).

* `MExp m` : multiplicity expressions `π, μ ::= 1 | ω | p | π + μ | π · μ` with `m`
  multiplicity variables in scope (de Bruijn indices; `MExp 0` holds closed multiplicities).
* `MExp.Equiv` : the equivalence of Definition 3.4.
* `Mult m` : multiplicities, i.e. expressions modulo that equivalence (a quotient, so equal
  multiplicities are equal in Lean).
* `MAlg` : the algebras satisfying the laws of Definition 3.4 ("semirings without zero");
  `Mult.lift` is the evaluation of a multiplicity in such an algebra, and substitution of
  multiplicities for multiplicity variables (`Mult.subst`) is evaluation in `Mult m'`.
* `Usage m` : `Mult m` with an adjoined zero.  The paper's contexts may *omit* a variable;
  in the de Bruijn presentation every variable is present and an omitted variable has usage
  `0`.  `Usage m` is a commutative semiring, so that context addition `Γ + Δ` and scaling
  `π Γ` are the pointwise operations on usage vectors `Fin n → Usage m`.
* `V3` : the three-element semiring `{0, 1, ω}`, used to evaluate multiplicities and refute
  equations between them.
-/

@[expose] public section

namespace LH

-- [PAPER ▶ START] §3.1 › Figure 5 "Syntax of λq→": multiplicities `π, μ ::= 1 | ω | p | π + μ | π · μ`
/-- Multiplicity expressions with `m` multiplicity variables in scope. -/
inductive MExp (m : Nat) : Type
  | one : MExp m
  | omega : MExp m
  | var : Fin m → MExp m
  | add : MExp m → MExp m → MExp m
  | mul : MExp m → MExp m → MExp m
  deriving DecidableEq
-- [PAPER ◀ END] §3.1 › Figure 5 (multiplicities)

-- [PAPER ▶ START] §3.2 › Definition 3.4 "equivalence of multiplicities"
/-- The equivalence of multiplicities (Definition 3.4).  The paper calls it "the smallest
transitive and reflexive relation" obeying the listed laws; we also include symmetry and
congruence, which are clearly intended (multiplicities are said to be *quotiented* by it). -/
inductive MExp.Equiv {m : Nat} : MExp m → MExp m → Prop
  | refl (a) : Equiv a a
  | symm {a b} : Equiv a b → Equiv b a
  | trans {a b c} : Equiv a b → Equiv b c → Equiv a c
  | add_congr {a a' b b'} : Equiv a a' → Equiv b b' → Equiv (.add a b) (.add a' b')
  | mul_congr {a a' b b'} : Equiv a a' → Equiv b b' → Equiv (.mul a b) (.mul a' b')
  /-- `+` is associative and commutative -/
  | add_assoc (a b c) : Equiv (.add (.add a b) c) (.add a (.add b c))
  | add_comm (a b) : Equiv (.add a b) (.add b a)
  /-- `·` is associative and commutative -/
  | mul_assoc (a b c) : Equiv (.mul (.mul a b) c) (.mul a (.mul b c))
  | mul_comm (a b) : Equiv (.mul a b) (.mul b a)
  /-- `1` is the unit of `·` -/
  | one_mul (a) : Equiv (.mul .one a) a
  /-- `·` distributes over `+` -/
  | mul_add (a b c) : Equiv (.mul a (.add b c)) (.add (.mul a b) (.mul a c))
  /-- `ω · ω = ω` -/
  | omega_mul_omega : Equiv (.mul .omega .omega) .omega
  /-- `1 + 1 = 1 + ω = ω + ω = ω` -/
  | one_add_one : Equiv (.add .one .one) .omega
  | one_add_omega : Equiv (.add .one .omega) .omega
  | omega_add_omega : Equiv (.add .omega .omega) .omega
-- [PAPER ◀ END] §3.2 › Definition 3.4

-- [NOT IN PAPER ▶ START] the quotient, algebras of multiplicities, usages
instance MExp.setoid (m : Nat) : Setoid (MExp m) :=
  ⟨MExp.Equiv, ⟨MExp.Equiv.refl, MExp.Equiv.symm, MExp.Equiv.trans⟩⟩

/-- Multiplicities: multiplicity expressions modulo the equivalence of Definition 3.4. -/
def Mult (m : Nat) : Type := Quotient (MExp.setoid m)

/-- Algebras satisfying the laws of Definition 3.4. -/
class MAlg (R : Type) extends Add R, Mul R, One R where
  omega : R
  add_assoc' : ∀ a b c : R, a + b + c = a + (b + c)
  add_comm' : ∀ a b : R, a + b = b + a
  mul_assoc' : ∀ a b c : R, a * b * c = a * (b * c)
  mul_comm' : ∀ a b : R, a * b = b * a
  one_mul' : ∀ a : R, 1 * a = a
  mul_add' : ∀ a b c : R, a * (b + c) = a * b + a * c
  omega_mul_omega' : omega * omega = omega
  one_add_one' : (1 : R) + 1 = omega
  one_add_omega' : (1 : R) + omega = omega
  omega_add_omega' : omega + omega = omega

namespace MExp

variable {m : Nat}

/-- Evaluation of a multiplicity expression in an algebra, given values of the variables. -/
def eval {R : Type} [MAlg R] (ρ : Fin m → R) : MExp m → R
  | one => 1
  | omega => MAlg.omega
  | var i => ρ i
  | add a b => eval ρ a + eval ρ b
  | mul a b => eval ρ a * eval ρ b

theorem eval_sound {R : Type} [MAlg R] (ρ : Fin m → R) {a b : MExp m} (h : Equiv a b) :
    eval ρ a = eval ρ b := by
  induction h with
  | refl => rfl
  | symm _ ih => exact ih.symm
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  | add_congr _ _ ih₁ ih₂ => simp only [eval, ih₁, ih₂]
  | mul_congr _ _ ih₁ ih₂ => simp only [eval, ih₁, ih₂]
  | add_assoc => exact MAlg.add_assoc' _ _ _
  | add_comm => exact MAlg.add_comm' _ _
  | mul_assoc => exact MAlg.mul_assoc' _ _ _
  | mul_comm => exact MAlg.mul_comm' _ _
  | one_mul => exact MAlg.one_mul' _
  | mul_add => exact MAlg.mul_add' _ _ _
  | omega_mul_omega => exact MAlg.omega_mul_omega'
  | one_add_one => exact MAlg.one_add_one'
  | one_add_omega => exact MAlg.one_add_omega'
  | omega_add_omega => exact MAlg.omega_add_omega'

end MExp

namespace Mult

variable {m : Nat}

/-- The class of an expression. -/
def mk (a : MExp m) : Mult m := Quotient.mk _ a

theorem mk_eq_mk {a b : MExp m} : mk a = mk b ↔ MExp.Equiv a b := Quotient.eq

theorem ind {P : Mult m → Prop} (h : ∀ a, P (mk a)) (x : Mult m) : P x :=
  Quotient.ind h x

instance : One (Mult m) := ⟨mk .one⟩
/-- The multiplicity `ω`. -/
def omega : Mult m := mk .omega
/-- The multiplicity variable `p`. -/
def var (i : Fin m) : Mult m := mk (.var i)

instance : Add (Mult m) :=
  ⟨Quotient.map₂ MExp.add (fun _ _ h₁ _ _ h₂ => MExp.Equiv.add_congr h₁ h₂)⟩
instance : Mul (Mult m) :=
  ⟨Quotient.map₂ MExp.mul (fun _ _ h₁ _ _ h₂ => MExp.Equiv.mul_congr h₁ h₂)⟩

@[simp] theorem mk_one : mk (.one : MExp m) = 1 := rfl
@[simp] theorem mk_omega : mk (.omega : MExp m) = omega := rfl
@[simp] theorem mk_var (i : Fin m) : mk (.var i) = var i := rfl
@[simp] theorem mk_add (a b : MExp m) : mk (.add a b) = mk a + mk b := rfl
@[simp] theorem mk_mul (a b : MExp m) : mk (.mul a b) = mk a * mk b := rfl

instance : MAlg (Mult m) where
  omega := omega
  add_assoc' a b c := by
    induction a using ind; induction b using ind; induction c using ind
    exact mk_eq_mk.2 (.add_assoc _ _ _)
  add_comm' a b := by
    induction a using ind; induction b using ind
    exact mk_eq_mk.2 (.add_comm _ _)
  mul_assoc' a b c := by
    induction a using ind; induction b using ind; induction c using ind
    exact mk_eq_mk.2 (.mul_assoc _ _ _)
  mul_comm' a b := by
    induction a using ind; induction b using ind
    exact mk_eq_mk.2 (.mul_comm _ _)
  one_mul' a := by
    induction a using ind
    exact mk_eq_mk.2 (.one_mul _)
  mul_add' a b c := by
    induction a using ind; induction b using ind; induction c using ind
    exact mk_eq_mk.2 (.mul_add _ _ _)
  omega_mul_omega' := mk_eq_mk.2 .omega_mul_omega
  one_add_one' := mk_eq_mk.2 .one_add_one
  one_add_omega' := mk_eq_mk.2 .one_add_omega
  omega_add_omega' := mk_eq_mk.2 .omega_add_omega

@[simp] theorem malg_omega : (MAlg.omega : Mult m) = omega := rfl

theorem add_assoc (a b c : Mult m) : a + b + c = a + (b + c) := MAlg.add_assoc' a b c
theorem add_comm (a b : Mult m) : a + b = b + a := MAlg.add_comm' a b
theorem mul_assoc (a b c : Mult m) : a * b * c = a * (b * c) := MAlg.mul_assoc' a b c
theorem mul_comm (a b : Mult m) : a * b = b * a := MAlg.mul_comm' a b
@[simp] theorem one_mul (a : Mult m) : 1 * a = a := MAlg.one_mul' a
@[simp] theorem mul_one (a : Mult m) : a * 1 = a := by rw [mul_comm, one_mul]
theorem mul_add (a b c : Mult m) : a * (b + c) = a * b + a * c := MAlg.mul_add' a b c
theorem add_mul (a b c : Mult m) : (a + b) * c = a * c + b * c := by
  rw [mul_comm, mul_add, mul_comm c, mul_comm c]
@[simp] theorem omega_mul_omega : (omega : Mult m) * omega = omega := MAlg.omega_mul_omega'
@[simp] theorem one_add_one : (1 : Mult m) + 1 = omega := MAlg.one_add_one'
@[simp] theorem one_add_omega : (1 : Mult m) + omega = omega := MAlg.one_add_omega'
@[simp] theorem omega_add_one : (omega : Mult m) + 1 = omega := by rw [add_comm]; simp
@[simp] theorem omega_add_omega : (omega : Mult m) + omega = omega := MAlg.omega_add_omega'

/-- Evaluation of a multiplicity in an algebra satisfying the laws of Definition 3.4. -/
def lift {R : Type} [MAlg R] (ρ : Fin m → R) : Mult m → R :=
  Quotient.lift (MExp.eval ρ) (fun _ _ h => MExp.eval_sound ρ h)

section lift
variable {R : Type} [MAlg R] (ρ : Fin m → R)
@[simp] theorem lift_mk (a : MExp m) : lift ρ (mk a) = a.eval ρ := rfl
@[simp] theorem lift_one : lift ρ 1 = 1 := rfl
@[simp] theorem lift_omega : lift ρ omega = MAlg.omega := rfl
@[simp] theorem lift_var (i : Fin m) : lift ρ (var i) = ρ i := rfl
@[simp] theorem lift_add (a b : Mult m) : lift ρ (a + b) = lift ρ a + lift ρ b := by
  induction a using ind; induction b using ind; rfl
@[simp] theorem lift_mul (a b : Mult m) : lift ρ (a * b) = lift ρ a * lift ρ b := by
  induction a using ind; induction b using ind; rfl
end lift

/-- Substitution of multiplicities for multiplicity variables. -/
def subst {m' : Nat} (s : Fin m → Mult m') : Mult m → Mult m' := lift s

section subst
variable {m' : Nat} (s : Fin m → Mult m')
@[simp] theorem subst_one : subst s 1 = 1 := rfl
@[simp] theorem subst_omega : subst s omega = omega := rfl
@[simp] theorem subst_var (i : Fin m) : subst s (var i) = s i := rfl
@[simp] theorem subst_add (a b : Mult m) : subst s (a + b) = subst s a + subst s b :=
  lift_add s a b
@[simp] theorem subst_mul (a b : Mult m) : subst s (a * b) = subst s a * subst s b :=
  lift_mul s a b
end subst

theorem subst_subst {m' m'' : Nat} (s : Fin m → Mult m') (s' : Fin m' → Mult m'')
    (a : Mult m) : subst s' (subst s a) = subst (fun i => subst s' (s i)) a := by
  induction a using ind with
  | h a =>
    induction a with
    | one => rfl
    | omega => rfl
    | var i => rfl
    | add a b iha ihb =>
      rw [mk_add, subst_add, subst_add, iha, ihb, subst_add]
    | mul a b iha ihb =>
      rw [mk_mul, subst_mul, subst_mul, iha, ihb, subst_mul]

theorem subst_var_id (a : Mult m) : subst var a = a := by
  induction a using ind with
  | h a =>
    induction a with
    | one => rfl
    | omega => rfl
    | var i => rfl
    | add a b iha ihb => rw [mk_add, subst_add, iha, ihb]
    | mul a b iha ihb => rw [mk_mul, subst_mul, iha, ihb]

theorem lift_subst {R : Type} [MAlg R] {m' : Nat} (s : Fin m → Mult m') (ρ : Fin m' → R)
    (a : Mult m) : lift ρ (subst s a) = lift (fun i => lift ρ (s i)) a := by
  induction a using ind with
  | h a =>
    induction a with
    | one => rfl
    | omega => rfl
    | var i => rfl
    | add a b iha ihb => rw [mk_add, subst_add, lift_add, lift_add, iha, ihb]
    | mul a b iha ihb => rw [mk_mul, subst_mul, lift_mul, lift_mul, iha, ihb]

/-- Weakening of multiplicities: the new multiplicity variable has index `0`. -/
def wk (a : Mult m) : Mult (m + 1) := subst (fun i => var i.succ) a

/-- Lifting a substitution under a multiplicity binder. -/
def liftS {m' : Nat} (s : Fin m → Mult m') : Fin (m + 1) → Mult (m' + 1) :=
  Fin.cons (var 0) (fun i => wk (s i))

theorem subst_liftS_wk {m' : Nat} (s : Fin m → Mult m') (a : Mult m) :
    subst (liftS s) (wk a) = wk (subst s a) := by
  unfold wk
  rw [subst_subst, subst_subst]
  rfl

theorem subst_cons_wk (π : Mult m) (a : Mult m) : subst (Fin.cons π var) (wk a) = a := by
  unfold wk; rw [subst_subst]; exact subst_var_id a

end Mult

/-- Usages: multiplicities with an adjoined `0` (the usage of a variable that does not occur in
a context of the paper). -/
inductive Usage (m : Nat) : Type
  | zero : Usage m
  | nz : Mult m → Usage m

namespace Usage

variable {m : Nat}

instance : Zero (Usage m) := ⟨zero⟩
instance : One (Usage m) := ⟨nz 1⟩

/-- Addition of usages. -/
def add : Usage m → Usage m → Usage m
  | zero, u => u
  | nz a, zero => nz a
  | nz a, nz b => nz (a + b)

/-- Multiplication of usages. -/
def mul : Usage m → Usage m → Usage m
  | zero, _ => zero
  | nz _, zero => zero
  | nz a, nz b => nz (a * b)

instance : Add (Usage m) := ⟨add⟩
instance : Mul (Usage m) := ⟨mul⟩

@[simp] theorem zero_def : (zero : Usage m) = 0 := rfl
@[simp] theorem nz_add_nz (a b : Mult m) : nz a + nz b = nz (a + b) := rfl
@[simp] theorem nz_mul_nz (a b : Mult m) : nz a * nz b = nz (a * b) := rfl
@[simp] theorem one_def : (nz 1 : Usage m) = 1 := rfl

instance : CommSemiring (Usage m) where
  add_assoc a b c := by
    cases a <;> cases b <;> cases c <;> first | rfl | exact congrArg nz (Mult.add_assoc _ _ _)
  zero_add a := by cases a <;> rfl
  add_zero a := by cases a <;> rfl
  add_comm a b := by
    cases a <;> cases b <;> first | rfl | exact congrArg nz (Mult.add_comm _ _)
  mul_assoc a b c := by
    cases a <;> cases b <;> cases c <;> first | rfl | exact congrArg nz (Mult.mul_assoc _ _ _)
  one_mul a := by cases a <;> first | rfl | exact congrArg nz (Mult.one_mul _)
  mul_one a := by cases a <;> first | rfl | exact congrArg nz (Mult.mul_one _)
  zero_mul a := by cases a <;> rfl
  mul_zero a := by cases a <;> rfl
  left_distrib a b c := by
    cases a <;> cases b <;> cases c <;> first | rfl | exact congrArg nz (Mult.mul_add _ _ _)
  right_distrib a b c := by
    cases a <;> cases b <;> cases c <;> first | rfl | exact congrArg nz (Mult.add_mul _ _ _)
  mul_comm a b := by
    cases a <;> cases b <;> first | rfl | exact congrArg nz (Mult.mul_comm _ _)
  nsmul := nsmulRec

/-- The usage `ω`. -/
def omega : Usage m := nz Mult.omega

/-- Substitution of multiplicities for multiplicity variables in a usage. -/
def subst {m' : Nat} (s : Fin m → Mult m') : Usage m →+* Usage m' where
  toFun
    | zero => zero
    | nz a => nz (Mult.subst s a)
  map_one' := rfl
  map_mul' a b := by cases a <;> cases b <;> first | rfl | exact congrArg nz (Mult.subst_mul _ _ _)
  map_zero' := rfl
  map_add' a b := by cases a <;> cases b <;> first | rfl | exact congrArg nz (Mult.subst_add _ _ _)

@[simp] theorem subst_nz {m' : Nat} (s : Fin m → Mult m') (a : Mult m) :
    subst s (nz a) = nz (Mult.subst s a) := rfl
@[simp] theorem subst_omega {m' : Nat} (s : Fin m → Mult m') :
    subst s omega = omega := rfl

theorem subst_subst {m' m'' : Nat} (s : Fin m → Mult m') (s' : Fin m' → Mult m'')
    (u : Usage m) : subst s' (subst s u) = subst (fun i => Mult.subst s' (s i)) u := by
  cases u
  · rfl
  · exact congrArg nz (Mult.subst_subst _ _ _)

/-- Weakening of usages. -/
def wk : Usage m →+* Usage (m + 1) := subst (fun i => Mult.var i.succ)

theorem subst_liftS_wk {m' : Nat} (s : Fin m → Mult m') (u : Usage m) :
    subst (Mult.liftS s) (wk u) = wk (subst s u) := by
  cases u
  · rfl
  · exact congrArg nz (Mult.subst_liftS_wk _ _)

theorem subst_cons_wk (π : Mult m) (u : Usage m) : subst (Fin.cons π Mult.var) (wk u) = u := by
  cases u
  · rfl
  · exact congrArg nz (Mult.subst_cons_wk _ _)

end Usage

/-- The three-element semiring `{0, 1, ω}`. -/
inductive V3
  | zero
  | one
  | omega
  deriving DecidableEq, Repr

namespace V3

/-- Addition: `0 + v = v`, `1 + 1 = ω`, `ω + v = ω`. -/
def add : V3 → V3 → V3
  | zero, v => v
  | v, zero => v
  | _, _ => omega

/-- Multiplication: `0 · v = 0`, `1 · v = v`, `ω · ω = ω`. -/
def mul : V3 → V3 → V3
  | zero, _ => zero
  | _, zero => zero
  | one, v => v
  | v, one => v
  | omega, omega => omega

instance : Add V3 := ⟨add⟩
instance : Mul V3 := ⟨mul⟩
instance : One V3 := ⟨one⟩
instance : Zero V3 := ⟨zero⟩

instance : MAlg V3 where
  omega := omega
  add_assoc' a b c := by cases a <;> cases b <;> cases c <;> rfl
  add_comm' a b := by cases a <;> cases b <;> rfl
  mul_assoc' a b c := by cases a <;> cases b <;> cases c <;> rfl
  mul_comm' a b := by cases a <;> cases b <;> rfl
  one_mul' a := by cases a <;> rfl
  mul_add' a b c := by cases a <;> cases b <;> cases c <;> rfl
  omega_mul_omega' := rfl
  one_add_one' := rfl
  one_add_omega' := rfl
  omega_add_omega' := rfl

instance : CommSemiring V3 where
  add_assoc a b c := by cases a <;> cases b <;> cases c <;> rfl
  zero_add a := by cases a <;> rfl
  add_zero a := by cases a <;> rfl
  add_comm a b := by cases a <;> cases b <;> rfl
  mul_assoc a b c := by cases a <;> cases b <;> cases c <;> rfl
  one_mul a := by cases a <;> rfl
  mul_one a := by cases a <;> rfl
  zero_mul a := by cases a <;> rfl
  mul_zero a := by cases a <;> rfl
  left_distrib a b c := by cases a <;> cases b <;> cases c <;> rfl
  right_distrib a b c := by cases a <;> cases b <;> cases c <;> rfl
  mul_comm a b := by cases a <;> cases b <;> rfl
  nsmul := nsmulRec

@[simp] theorem malg_omega : (MAlg.omega : V3) = omega := rfl

end V3

namespace Usage

variable {m : Nat}

/-- Evaluation of a usage in `{0, 1, ω}`, given values of the multiplicity variables. -/
def eval (ρ : Fin m → V3) : Usage m →+* V3 where
  toFun
    | zero => 0
    | nz a => Mult.lift ρ a
  map_one' := rfl
  map_mul' a b := by
    cases a <;> cases b
    · rfl
    · exact (zero_mul _).symm
    · exact (mul_zero _).symm
    · exact Mult.lift_mul _ _ _
  map_zero' := rfl
  map_add' a b := by
    cases a <;> cases b
    · rfl
    · exact (zero_add _).symm
    · exact (add_zero _).symm
    · exact Mult.lift_add _ _ _

@[simp] theorem eval_nz (ρ : Fin m → V3) (a : Mult m) : eval ρ (nz a) = Mult.lift ρ a := rfl
@[simp] theorem eval_omega (ρ : Fin m → V3) : eval ρ omega = V3.omega := rfl

end Usage

/-- A multiplicity never evaluates to `0` when all variables are sent to `1` or `ω`. -/
theorem Mult.lift_ne_zero {m : Nat} (ρ : Fin m → V3) (hρ : ∀ i, ρ i ≠ V3.zero)
    (a : Mult m) : Mult.lift ρ a ≠ V3.zero := by
  induction a using Mult.ind with
  | h a =>
    induction a with
    | one => exact fun h => by cases h
    | omega => exact fun h => by cases h
    | var i => exact hρ i
    | add a b iha ihb =>
      rw [Mult.mk_add, Mult.lift_add]
      revert iha ihb
      cases Mult.lift ρ (Mult.mk a) <;> cases Mult.lift ρ (Mult.mk b) <;> decide
    | mul a b iha ihb =>
      rw [Mult.mk_mul, Mult.lift_mul]
      revert iha ihb
      cases Mult.lift ρ (Mult.mk a) <;> cases Mult.lift ρ (Mult.mk b) <;> decide

-- [NOT IN PAPER ◀ END]

end LH

namespace LH

-- [NOT IN PAPER ▶ START] closed multiplicities
/-- Every closed multiplicity is `1` or `ω` (so with no multiplicity variables the
multiplicities of `λq→` are exactly the two multiplicities `{1, ω}`). -/
theorem Mult.closed_cases (a : Mult 0) : a = 1 ∨ a = Mult.omega := by
  induction a using Mult.ind with
  | h a =>
    induction a with
    | one => exact .inl rfl
    | omega => exact .inr rfl
    | var i => exact i.elim0
    | add a b iha ihb =>
      rw [Mult.mk_add]
      rcases iha with h | h <;> rcases ihb with h' | h' <;> rw [h, h'] <;> simp
    | mul a b iha ihb =>
      rw [Mult.mk_mul]
      rcases iha with h | h <;> rcases ihb with h' | h' <;> rw [h, h'] <;> simp

/-- `1 ≠ ω` (for any number of multiplicity variables). -/
theorem Mult.one_ne_omega {m : Nat} : (1 : Mult m) ≠ Mult.omega := by
  intro h
  have := congrArg (Mult.lift (fun _ => V3.one)) h
  simp at this

/-- Evaluation of closed usages in `{0, 1, ω}` is injective. -/
theorem Usage.eval0_injective : Function.Injective (Usage.eval (Fin.elim0 : Fin 0 → V3)) := by
  intro a b h
  cases a with
  | zero =>
    cases b with
    | zero => rfl
    | nz b' =>
      rcases Mult.closed_cases b' with rfl | rfl <;> cases h
  | nz a' =>
    cases b with
    | zero => rcases Mult.closed_cases a' with rfl | rfl <;> cases h
    | nz b' =>
      rcases Mult.closed_cases a' with rfl | rfl <;> rcases Mult.closed_cases b' with rfl | rfl <;>
        first | rfl | cases h
-- [NOT IN PAPER ◀ END]

end LH
