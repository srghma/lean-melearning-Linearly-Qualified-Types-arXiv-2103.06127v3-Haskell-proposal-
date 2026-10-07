module

public import RequestProject.LQT.Ch5_QualifiedTypeSystem.Entailment
public import RequestProject.LQT.Infrastructure.Map

/-!
# Type-variable levels: families of constraint domains

**Type variables.**  With type polymorphism, atomic constraints mention type variables (as in
`RW n`).  Type variables are de Bruijn indices: `A k` is the set of atomic constraints with
`k` type variables in scope, and atoms can be *weakened* to a larger scope (`Weakening`).
Accordingly the constraint domain is a family of domains `D k` (`LDomain`), one for each
number of type variables in scope.  `LDomain.Lawful` requires each domain to be lawful and
entailment to be stable under weakening.

Paper location: none.  The paper has no explicit scopes for type variables; this file extends
the domains of Definition 5.3 (§5.1) to families indexed by the number of type variables.
-/

@[expose] public section

namespace LQT

open SConstr

-- [NOT IN PAPER ▶ START] type-variable levels: weakening of atoms and families of domains `LDomain`
--   (the paper has no explicit scopes for type variables)
/-- A family of sets of atomic constraints, indexed by the number of type variables in scope,
with weakening of atoms to a larger scope (the new variables are added at the end). -/
class Weakening (A : Nat → Type) where
  /-- Weakening of an atom by `j` new type variables. -/
  wk : {k : Nat} → (j : Nat) → A k → A (k + j)

variable {A : Nat → Type} [∀ k, DecidableEq (A k)] [Weakening A]

/-- Weakening of a simple constraint by `j` new type variables. -/
def SConstr.wk {k : Nat} (j : Nat) (Q : SConstr (A k)) : SConstr (A (k + j)) :=
  Q.map (Weakening.wk j)

@[simp] lemma SConstr.wk_zero {k j : Nat} : (0 : SConstr (A k)).wk j = 0 := map_zero _
@[simp] lemma SConstr.wk_add {k j : Nat} (Q₁ Q₂ : SConstr (A k)) :
    (Q₁ + Q₂).wk j = Q₁.wk j + Q₂.wk j := map_add _ _ _
@[simp] lemma SConstr.wk_smul {k j : Nat} (π : Mult) (Q : SConstr (A k)) :
    (π • Q).wk j = π • Q.wk j := map_smul _ _ _

/-- A constraint domain for each number of type variables in scope. -/
abbrev LDomain (A : Nat → Type) := (k : Nat) → Domain (A k)

/-- Lawful families of domains: each domain is lawful, and duplicability and entailment are
stable under weakening (the usual stability of entailment under renaming of type
variables). -/
structure LDomain.Lawful (D : LDomain A) : Prop where
  lawful : ∀ k, (D k).Lawful
  dup_wk : ∀ {k : Nat} (j : Nat) {q : A k}, q ∈ (D k).Dup → Weakening.wk j q ∈ (D (k + j)).Dup
  entails_wk : ∀ {k : Nat} (j : Nat) {Q Q' : SConstr (A k)}, (D k).Entails Q Q' →
    (D (k + j)).Entails (Q.wk j) (Q'.wk j)

-- [NOT IN PAPER ◀ END] type-variable levels

end LQT
