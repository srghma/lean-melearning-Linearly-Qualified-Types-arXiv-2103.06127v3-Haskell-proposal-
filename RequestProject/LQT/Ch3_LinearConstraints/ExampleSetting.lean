module

public import RequestProject.LQT.Ch6_ConstraintInference.FreeLDomain
public import RequestProject.LQT.Ch5_QualifiedTypeSystem.Typing

/-!
# The setting of the examples (§3.1)

Paper location: §3.1 "Minimal Examples" (the setting: a linear constraint `C` consumed by
`useC :: C ⊸ Int`, and the linear `const :: a ⊸ b → a`).  The same setting is reused by the
examples of §5.2, §6.1 and §6.3.2.  We write it in the formalized language:

* one predicate symbol (`P = Unit`), giving the atomic constraint `C`;
* the constraint domain is the stripped-down domain of Figure 10a with no duplicable atom
  (`predLDomain ∅`), so `C` is genuinely linear;
* the data types `Int` (one nullary constructor `ten`, standing for the literal `10`), `Bool`
  (constructors `True`, `False`) and linear pairs `(a, b)` (one constructor with two linear
  fields);
* the top-level definitions `useC : ∀. C ⊸ Int` and `const : ∀a b. a →₁ b →ω a` are the two
  variables of the context (de Bruijn indices `0` and `1`), with arbitrary usage;
* the given constraint `C` (from the signatures `… :: C ⊸ …`) is the linear assumption
  `1·C`.

The helper `ent_count` is the counting argument used to reject programs: in this domain,
entailment from a constraint in which `C` is not unrestricted preserves the number of linear
copies of `C`.
-/

@[expose] public section

namespace LQT

namespace Examples

-- [PAPER ▶ START] §3.1 "Minimal Examples": the setting (constraint `C`, `useC`, `const`, data
--   types `Int`, `Bool` and pairs)

/-- The atomic constraint `C`. -/
def cAtom {k : Nat} : Atom Unit k := ((), [])

/-- The given constraint `C` (a single linear copy). -/
def givenC {k : Nat} : SConstr (Atom Unit k) := SConstr.atom .one cAtom

/-- The constraint domain: the stripped-down domain of Figure 10a with no duplicable atoms. -/
def exD : LDomain (Atom Unit) := predLDomain ∅

/-- Number of type parameters of the data types: `Int` (`0`), `Bool` (`1`), pairs (`2`). -/
def exParams : Nat → Nat
  | 2 => 2
  | _ => 0

/-- Number of constructors: `Int` has `ten`, `Bool` has `True`/`False`, pairs have `(,)`. -/
def exNcons : Nat → Nat
  | 0 => 1
  | 1 => 2
  | 2 => 1
  | _ => 0

/-- Number of fields of the constructors (only the pair constructor has fields). -/
def exArity : (T : Nat) → Fin (exNcons T) → Nat
  | 2, _ => 2
  | _, _ => 0

/-- Fields of the constructors: the pair constructor has two *linear* fields of types `a`, `b`. -/
def exField : (T : Nat) → (i : Fin (exNcons T)) → Fin (exArity T i) → Mult × Ty Unit (exParams T)
  | 0, _, l => l.elim0
  | 1, _, l => l.elim0
  | 2, _, l => (.one, .tvar l)
  | _ + 3, i, _ => i.elim0

/-- The data type signature of the examples. -/
def exSig : DataSig Unit := ⟨exParams, exNcons, exArity, exField⟩

/-- The type `Int`. -/
def intTy {k : Nat} : Ty Unit k := .data 0 0 (fun l => l.elim0)

/-- The type `Bool`. -/
def boolTy {k : Nat} : Ty Unit k := .data 1 0 (fun l => l.elim0)

/-- The scheme of `useC :: C ⊸ Int`. -/
def useCScheme : Scheme Unit 0 := ⟨0, givenC, intTy⟩

/-- The scheme of `const :: a ⊸ b → a`. -/
def constScheme : Scheme Unit 0 :=
  ⟨2, 0, .arr .one (.tvar 0) (.arr .omega (.tvar 1) (.tvar 0))⟩

/-- The context: `useC` (index `0`) and `const` (index `1`). -/
def exΓ : Fin 2 → Scheme Unit 0 := ![useCScheme, constScheme]

-- [PAPER ◀ END] §3.1, the setting

-- [NOT IN PAPER ▶ START] helpers for the proofs of the examples

lemma exD_lawful : ∀ k, (exD k).Lawful := (predLDomain_lawful ∅).lawful

@[simp] lemma givenC_U {k : Nat} : (givenC : SConstr (Atom Unit k)).U = ∅ := rfl
@[simp] lemma givenC_L {k : Nat} : (givenC : SConstr (Atom Unit k)).L = {cAtom} := rfl

@[simp] lemma givenC_tsubst {k k' : Nat} (σ : Fin k → Ty Unit k') :
    (givenC : SConstr (Atom Unit k)).tsubst σ = givenC := by
  simp only [givenC, SConstr.tsubst, SConstr.map_atom]; rfl

/-- In the domain of the examples, entailment from a constraint in which `C` is not
unrestricted preserves the number of linear copies of `C` (and keeps `C` non-unrestricted). -/
lemma ent_count {k : Nat} {Q R : SConstr (Atom Unit k)} (h : (exD k).Entails Q R)
    (hc : cAtom ∉ Q.U) : cAtom ∉ R.U ∧ R.L.count cAtom = Q.L.count cAtom := by
  obtain ⟨hU, hN, -⟩ := h
  refine ⟨fun h' => hc (hU h'), ?_⟩
  obtain ⟨h₁, h₂⟩ := hN cAtom (by simp)
  by_contra hne
  exact hc (h₂ (lt_of_le_of_ne h₁ (Ne.symm hne)))


@[simp] lemma intTy_subst {k k' : Nat} (σ : Fin k → Ty Unit k') :
    (intTy : Ty Unit k).subst σ = intTy := by
  simp only [intTy, Ty.subst]
  congr 1; funext l; exact l.elim0

-- [NOT IN PAPER ◀ END] helpers

end Examples

end LQT
