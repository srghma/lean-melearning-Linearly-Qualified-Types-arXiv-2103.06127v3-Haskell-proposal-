module

public import RequestProject.LH.Multiplicity
public import RequestProject.LQT.Infrastructure.Usage

/-!
# Relating the multiplicities of the two papers

No counterpart in either paper.  *Linearly Qualified Types* (formalized in `RequestProject/LQT`)
uses only the two multiplicities `1` and `ω` (`LQT.Mult`), while the core calculus `λq→` of
*Linear Haskell* (formalized in `RequestProject/LH`) has multiplicity variables, sums and
products, quotiented by the equivalence of its Definition 3.4 (`LH.Mult m`).

* `LH.closedMultEquiv` : the closed multiplicities of `λq→` (no multiplicity variables) are
  exactly `{1, ω}`: `LH.Mult 0 ≃ LQT.Mult`, and the bijection preserves products.
* `LH.closedUsageEquiv` : likewise the closed usages of `λq→` (with the adjoined `0`) are exactly
  the usages `{0, 1, ω}` of the de Bruijn presentation of `RequestProject/LQT`, and the bijection
  preserves sums.
-/

@[expose] public section

namespace LH

-- [NOT IN PAPER ▶ START] comparison of the multiplicities of the two papers
/-- From closed multiplicities of `λq→` to the multiplicities of *Linearly Qualified Types*. -/
def toLQTMult (a : Mult 0) : LQT.Mult :=
  match Mult.lift (R := V3) Fin.elim0 a with
  | V3.one => LQT.Mult.one
  | _ => LQT.Mult.omega

/-- From the multiplicities of *Linearly Qualified Types* to closed multiplicities of `λq→`. -/
def ofLQTMult : LQT.Mult → Mult 0
  | .one => 1
  | .omega => Mult.omega

/-- The closed multiplicities of `λq→` are exactly the multiplicities `{1, ω}` of *Linearly
Qualified Types*. -/
def closedMultEquiv : Mult 0 ≃ LQT.Mult where
  toFun := toLQTMult
  invFun := ofLQTMult
  left_inv a := by
    rcases Mult.closed_cases a with rfl | rfl <;> rfl
  right_inv p := by cases p <;> rfl

/-- The bijection preserves products. -/
theorem closedMultEquiv_mul (a b : Mult 0) :
    closedMultEquiv (a * b) = closedMultEquiv a * closedMultEquiv b := by
  rcases Mult.closed_cases a with rfl | rfl <;> rcases Mult.closed_cases b with rfl | rfl <;>
    simp <;> rfl

/-- From closed usages of `λq→` to the usages `{0, 1, ω}` of `RequestProject/LQT`. -/
def toLQTUsage : Usage 0 → LQT.Usage
  | .zero => LQT.Usage.zero
  | .nz a => LQT.Usage.ofMult (closedMultEquiv a)

/-- From the usages `{0, 1, ω}` of `RequestProject/LQT` to closed usages of `λq→`. -/
def ofLQTUsage : LQT.Usage → Usage 0
  | .zero => 0
  | .one => 1
  | .omega => Usage.omega

/-- The closed usages of `λq→` are exactly the usages `{0, 1, ω}`. -/
def closedUsageEquiv : Usage 0 ≃ LQT.Usage where
  toFun := toLQTUsage
  invFun := ofLQTUsage
  left_inv u := by
    cases u with
    | zero => rfl
    | nz a => rcases Mult.closed_cases a with rfl | rfl <;> rfl
  right_inv p := by cases p <;> rfl

/-- The bijection preserves sums. -/
theorem closedUsageEquiv_add (u v : Usage 0) :
    closedUsageEquiv (u + v) = closedUsageEquiv u + closedUsageEquiv v := by
  cases u with
  | zero => cases v <;> rfl
  | nz a =>
    cases v with
    | zero => rcases Mult.closed_cases a with rfl | rfl <;> rfl
    | nz b =>
      rcases Mult.closed_cases a with rfl | rfl <;> rcases Mult.closed_cases b with rfl | rfl <;>
        simp [closedUsageEquiv, toLQTUsage] <;> rfl
-- [NOT IN PAPER ◀ END]

end LH
