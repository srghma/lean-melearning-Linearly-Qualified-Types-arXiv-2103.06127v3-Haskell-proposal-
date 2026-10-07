module

public import Mathlib

/-!
# Multiplicities (§2.1)

Paper location: §2.1 "Multiplicities": the grammar `π, ρ ::= 1 | ω` and the product `π⋅ρ`.
The start and end of each part is marked by `-- [PAPER ▶ START]` / `-- [PAPER ◀ END]` comments;
material that has no counterpart in the paper is marked `-- [NOT IN PAPER ▶ START]` /
`-- [NOT IN PAPER ◀ END]`.

* `Mult` : the multiplicities `1` and `ω` that annotate arrows, binders and constraints.
-/

@[expose] public section

namespace LQT

-- [PAPER ▶ START] §2.1 "Multiplicities": the grammar `π, ρ ::= 1 | ω` and the product `π⋅ρ`
/-! ## Multiplicities -/

/-- Multiplicities `π, ρ ::= 1 | ω`. -/
inductive Mult
  | one
  | omega
  deriving DecidableEq, Repr

namespace Mult

/-- Multiplication of multiplicities: `1 · π = π`, `ω · π = ω`. -/
def mul : Mult → Mult → Mult
  | one, p => p
  | omega, _ => omega

instance : Mul Mult := ⟨mul⟩
instance : One Mult := ⟨one⟩

@[simp] lemma one_def : (1 : Mult) = one := rfl
@[simp] lemma one_mul' (p : Mult) : one * p = p := rfl
@[simp] lemma omega_mul (p : Mult) : omega * p = omega := rfl
@[simp] lemma mul_omega (p : Mult) : p * omega = omega := by cases p <;> rfl
@[simp] lemma mul_one' (p : Mult) : p * one = p := by cases p <;> rfl

instance : CommMonoid Mult where
  mul_assoc a b c := by cases a <;> cases b <;> cases c <;> rfl
  one_mul a := by cases a <;> rfl
  mul_one a := by cases a <;> rfl
  mul_comm a b := by cases a <;> cases b <;> rfl

lemma mul_self (p : Mult) : p * p = p := by cases p <;> rfl

end Mult

-- [PAPER ◀ END] §2.1 "Multiplicities"

end LQT
