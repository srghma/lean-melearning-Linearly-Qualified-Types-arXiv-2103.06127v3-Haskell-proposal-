module

public import RequestProject.LQT.Ch2_Background.Multiplicities

/-!
# Usages: the semiring `{0, 1, ω}`

* `Usage` : the semiring `{0, 1, ω}` used for the *usage vectors* of the de Bruijn
  presentation of typing contexts (a variable that does not occur in a context of the paper
  has usage `0` here).

Paper location: none.  Usage vectors replace the named contexts of the paper: context scaling
`π·Γ` and context addition `Γ₁ + Γ₂` (defined below the grammar in Figure 5, §5.2) become
pointwise operations on usage vectors.
-/

@[expose] public section

namespace LQT

-- [NOT IN PAPER ▶ START] usages `{0, 1, ω}` and usage vectors. They replace the named contexts of
--   the paper: context scaling `π·Γ` and context addition `Γ₁ + Γ₂` (defined below the grammar in
--   Figure 5, §5.2) become pointwise operations on usage vectors
/-! ## Usages: the semiring `{0, 1, ω}` -/

/-- Usages of a variable in a (de Bruijn) context: `0` (absent), `1` (linear) or `ω`. -/
inductive Usage
  | zero
  | one
  | omega
  deriving DecidableEq, Repr

namespace Usage

/-- Addition of usages: `0 + u = u`, `1 + 1 = ω`, `ω + u = ω`. -/
def add : Usage → Usage → Usage
  | zero, u => u
  | u, zero => u
  | _, _ => omega

instance : Add Usage := ⟨add⟩
instance : Zero Usage := ⟨zero⟩

@[simp] lemma zero_eq : (zero : Usage) = 0 := rfl

instance : AddCommMonoid Usage where
  add_assoc a b c := by cases a <;> cases b <;> cases c <;> rfl
  zero_add a := by cases a <;> rfl
  add_zero a := by cases a <;> rfl
  add_comm a b := by cases a <;> cases b <;> rfl
  nsmul := nsmulRec

/-- The usage corresponding to a multiplicity. -/
def ofMult : Mult → Usage
  | .one => one
  | .omega => omega

instance : Coe Mult Usage := ⟨ofMult⟩

/-- Scaling a usage by a multiplicity. -/
def smul : Mult → Usage → Usage
  | .one, u => u
  | .omega, zero => zero
  | .omega, _ => omega

instance : SMul Mult Usage := ⟨smul⟩

instance : DistribMulAction Mult Usage where
  one_smul u := rfl
  mul_smul a b u := by cases a <;> cases b <;> cases u <;> rfl
  smul_zero a := by cases a <;> rfl
  smul_add a u v := by cases a <;> cases u <;> cases v <;> rfl

@[simp] lemma one_smul' (u : Usage) : (Mult.one : Mult) • u = u := rfl
@[simp] lemma omega_smul_zero : (Mult.omega : Mult) • (0 : Usage) = 0 := rfl
@[simp] lemma omega_smul_one : (Mult.omega : Mult) • Usage.one = Usage.omega := rfl
@[simp] lemma omega_smul_omega : (Mult.omega : Mult) • Usage.omega = Usage.omega := rfl
@[simp] lemma ofMult_one : ofMult Mult.one = Usage.one := rfl
@[simp] lemma ofMult_omega : ofMult Mult.omega = Usage.omega := rfl
@[simp] lemma one_add_one : Usage.one + Usage.one = Usage.omega := rfl
@[simp] lemma omega_add (u : Usage) : Usage.omega + u = Usage.omega := by cases u <;> rfl
@[simp] lemma add_omega (u : Usage) : u + Usage.omega = Usage.omega := by cases u <;> rfl

end Usage

/-- The usage vector in which only the variable `x` is used, once. -/
def single {n : Nat} (x : Fin n) : Fin n → Usage :=
  fun y => if y = x then Usage.one else 0

-- [NOT IN PAPER ◀ END] usages

end LQT
