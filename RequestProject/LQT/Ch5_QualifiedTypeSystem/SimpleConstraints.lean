module

public import RequestProject.LQT.Ch2_Background.Multiplicities

/-!
# Simple constraints (§5.1, Definition 5.2)

Paper location: §5.1 "Simple Constraints and Entailment" (Definition 5.2 "Simple constraints",
the scaling `π·Q`, the notation `Q ∈ 𝒟` of Definition 5.3, the predicate "no linear assumptions"
of Corollary 5.6) and Appendix B.5 (Lemma B.1).  The start and end of each part is marked by
`-- [PAPER ▶ START]` / `-- [PAPER ◀ END]` comments.

* `SConstr A` : simple constraints `Q = (U, L)`, a finite set `U` of unrestricted atomic
  constraints together with a multiset `L` of linear atomic constraints.  The tensor product
  `Q₁ ⊗ Q₂` of the paper is written `Q₁ + Q₂` and the empty conjunction `ε` is written `0`;
  scaling `π · Q` is written `π • Q`.
-/

@[expose] public section

namespace LQT

/-! ## Simple constraints -/

-- [PAPER ▶ START] §5.1 › Definition 5.2 "Simple constraints": `Q ::= (U, L)`, `ε = (∅, ∅)` and the
--   tensor `(U₁, L₁) ⊗ (U₂, L₂)` (the scaled atoms `π·q` are `atom`, below)
/-- Simple constraints `Q = (U, L)`: a finite set `U` of unrestricted atomic constraints and a
multiset `L` of linear atomic constraints.  The set of atomic constraints `A` is a parameter. -/
@[ext]
structure SConstr (A : Type*) where
  /-- The unrestricted atomic constraints. -/
  U : Finset A
  /-- The linear atomic constraints. -/
  L : Multiset A
  deriving DecidableEq

namespace SConstr

/-- The empty conjunction `ε = (∅, ∅)`, written `0`. -/
instance {A : Type*} : Zero (SConstr A) := ⟨⟨∅, 0⟩⟩

@[simp] lemma zero_U {A : Type*} : (0 : SConstr A).U = ∅ := rfl
@[simp] lemma zero_L {A : Type*} : (0 : SConstr A).L = 0 := rfl

variable {A : Type*} [DecidableEq A]

/-- The tensor product `(U₁, L₁) ⊗ (U₂, L₂) = (U₁ ∪ U₂, L₁ ⊎ L₂)`, written `+`. -/
instance : Add (SConstr A) := ⟨fun Q₁ Q₂ => ⟨Q₁.U ∪ Q₂.U, Q₁.L + Q₂.L⟩⟩

@[simp] lemma add_U (Q₁ Q₂ : SConstr A) : (Q₁ + Q₂).U = Q₁.U ∪ Q₂.U := rfl
@[simp] lemma add_L (Q₁ Q₂ : SConstr A) : (Q₁ + Q₂).L = Q₁.L + Q₂.L := rfl

instance : AddCommMonoid (SConstr A) where
  add_assoc a b c := by ext <;> simp [Finset.union_assoc, add_assoc]
  zero_add a := by ext <;> simp
  add_zero a := by ext <;> simp
  add_comm a b := by ext <;> simp [Finset.union_comm, add_comm]
  nsmul := nsmulRec

-- [PAPER ◀ END] §5.1 › Definition 5.2 (`Q`, `ε`, `⊗`)

-- [PAPER ▶ START] §5.1, text between Definition 5.3 and Lemma 5.4: "Define `π·Q` as" `1·(U, L) =
--   (U, L)`, `ω·(U, L) = (U ∪ L, ∅)`
/-- Scaling of simple constraints: `1 · (U, L) = (U, L)` and `ω · (U, L) = (U ∪ L, ∅)`. -/
def smul : Mult → SConstr A → SConstr A
  | .one, Q => Q
  | .omega, Q => ⟨Q.U ∪ Q.L.toFinset, 0⟩

instance : SMul Mult (SConstr A) := ⟨smul⟩

@[simp] lemma one_smul' (Q : SConstr A) : (Mult.one : Mult) • Q = Q := rfl
@[simp] lemma omega_smul_U (Q : SConstr A) :
    ((Mult.omega : Mult) • Q).U = Q.U ∪ Q.L.toFinset := rfl
@[simp] lemma omega_smul_L (Q : SConstr A) : ((Mult.omega : Mult) • Q).L = 0 := rfl
lemma smul_def (p : Mult) (Q : SConstr A) : p • Q = smul p Q := rfl

-- [PAPER ◀ END] §5.1, definition of `π·Q`

-- [PAPER ▶ START] Appendix B.5 › Lemma B.1: `π·(ρ·Q) = (π⋅ρ)·Q` (the `mul_smul` field below; the
--   other fields are not in the paper)
instance : DistribMulAction Mult (SConstr A) where
  one_smul _ := rfl
  mul_smul a b Q := by
    cases a <;> cases b
    · rfl
    · rfl
    · rfl
    · ext <;> simp [smul_def, smul]
  smul_zero a := by
    cases a
    · rfl
    · apply SConstr.ext <;> simp
  smul_add a Q₁ Q₂ := by
    cases a
    · rfl
    · apply SConstr.ext
      · simp only [omega_smul_U, add_U, add_L, Multiset.toFinset_add]
        ext x; simp only [Finset.mem_union]; tauto
      · simp

-- [PAPER ◀ END] Appendix B.5 › Lemma B.1

-- [PAPER ▶ START] §5.1 › Definition 5.2 "Simple constraints": scaled atomic constraints `1·q = (∅,
--   q)`, `ω·q = (q, ∅)`
/-- A scaled atomic constraint `π · q`: `1 · q = (∅, {q})` and `ω · q = ({q}, ∅)`. -/
def atom : Mult → A → SConstr A
  | .one, q => ⟨∅, {q}⟩
  | .omega, q => ⟨{q}, 0⟩

-- [PAPER ◀ END] §5.1 › Definition 5.2 (scaled atomic constraints)

-- [NOT IN PAPER ▶ START] the unrestricted and linear parts of a simple constraint
/-- The unrestricted part `(U, ∅)` of a simple constraint. -/
def unr (Q : SConstr A) : SConstr A := ⟨Q.U, 0⟩

/-- The linear part `(∅, L)` of a simple constraint. -/
def lin (Q : SConstr A) : SConstr A := ⟨∅, Q.L⟩

-- [NOT IN PAPER ◀ END] unrestricted and linear parts

-- [PAPER ▶ START] §5.1 › Definition 5.3 "Entailment relation": the notation `Q ∈ 𝒟` ("abusing
--   notation")
/-- `Q ∈ 𝒟` for a set `𝒟` of atomic constraints: every *linear* atomic constraint of `Q`
belongs to `𝒟` (the unrestricted part is arbitrary). -/
def InDup (S : Set A) (Q : SConstr A) : Prop := ∀ q ∈ Q.L, q ∈ S

-- [PAPER ◀ END] §5.1 › Definition 5.3 (notation `Q ∈ 𝒟`)

-- [PAPER ▶ START] §5.1 › Corollary 5.6 "Linear assumptions": "`Q₁` contains no linear assumptions"
/-- A simple constraint is *unrestricted* when it has no linear part. -/
def Unrestricted (Q : SConstr A) : Prop := Q.L = 0

-- [PAPER ◀ END] §5.1 › Corollary 5.6 (the predicate "no linear assumptions")

-- [NOT IN PAPER ▶ START] basic algebraic facts about simple constraints, used by the proofs
/-! ### Basic facts about simple constraints -/

omit [DecidableEq A] in
@[simp] lemma atom_one_U (q : A) : (atom .one q).U = ∅ := rfl
omit [DecidableEq A] in
@[simp] lemma atom_one_L (q : A) : (atom .one q).L = {q} := rfl
omit [DecidableEq A] in
@[simp] lemma atom_omega_U (q : A) : (atom .omega q).U = {q} := rfl
omit [DecidableEq A] in
@[simp] lemma atom_omega_L (q : A) : (atom .omega q).L = 0 := rfl
omit [DecidableEq A] in
@[simp] lemma unr_U (Q : SConstr A) : Q.unr.U = Q.U := rfl
omit [DecidableEq A] in
@[simp] lemma unr_L (Q : SConstr A) : Q.unr.L = 0 := rfl
omit [DecidableEq A] in
@[simp] lemma lin_U (Q : SConstr A) : Q.lin.U = ∅ := rfl
omit [DecidableEq A] in
@[simp] lemma lin_L (Q : SConstr A) : Q.lin.L = Q.L := rfl

/-- Scaling of scaled atoms: `π · (ρ · q) = (π ⋅ ρ) · q`. -/
lemma smul_atom (p r : Mult) (q : A) : p • atom r q = atom (p * r) q := by
  cases p <;> cases r <;> rfl

lemma unr_add_lin (Q : SConstr A) : Q = Q.unr + Q.lin := by
  ext <;> simp

lemma omega_smul_of_unrestricted {Q : SConstr A} (h : Q.Unrestricted) :
    (Mult.omega : Mult) • Q = Q := by
  unfold Unrestricted at h
  ext <;> simp [h]

lemma add_self_of_unrestricted {Q : SConstr A} (h : Q.Unrestricted) : Q + Q = Q := by
  unfold Unrestricted at h
  ext <;> simp [h]

lemma unrestricted_omega_smul (Q : SConstr A) : ((Mult.omega : Mult) • Q).Unrestricted := rfl

omit [DecidableEq A] in
lemma unrestricted_unr (Q : SConstr A) : Q.unr.Unrestricted := rfl

omit [DecidableEq A] in
lemma unrestricted_zero : (0 : SConstr A).Unrestricted := rfl

lemma unrestricted_add {Q₁ Q₂ : SConstr A} (h₁ : Q₁.Unrestricted) (h₂ : Q₂.Unrestricted) :
    (Q₁ + Q₂).Unrestricted := by
  unfold Unrestricted at *; simp [h₁, h₂]

lemma omega_smul_unr (Q : SConstr A) : (Mult.omega : Mult) • Q.unr = Q.unr :=
  omega_smul_of_unrestricted (unrestricted_unr Q)

lemma omega_smul_add_self (Q : SConstr A) :
    (Mult.omega : Mult) • Q + (Mult.omega : Mult) • Q = (Mult.omega : Mult) • Q :=
  add_self_of_unrestricted (unrestricted_omega_smul Q)

/-- If an unrestricted `X` has its atoms among the unrestricted atoms of `Q`, then it is
absorbed by `Q.unr`. -/
lemma unr_add_absorb {Q X : SConstr A} (hX : X.Unrestricted) (hU : X.U ⊆ Q.U) :
    Q.unr + X = Q.unr := by
  unfold Unrestricted at hX
  ext x
  · simp only [add_U, unr_U, Finset.mem_union]
    constructor
    · rintro (h | h)
      · exact h
      · exact hU h
    · exact Or.inl
  · simp [hX]

omit [DecidableEq A] in
lemma inDup_zero (S : Set A) : (0 : SConstr A).InDup S := by
  intro q hq; simp at hq

lemma inDup_add_iff {S : Set A} {Q₁ Q₂ : SConstr A} :
    (Q₁ + Q₂).InDup S ↔ Q₁.InDup S ∧ Q₂.InDup S := by
  unfold InDup
  simp only [add_L, Multiset.mem_add]
  constructor
  · intro h; exact ⟨fun q hq => h q (Or.inl hq), fun q hq => h q (Or.inr hq)⟩
  · rintro ⟨h₁, h₂⟩ q (hq | hq)
    · exact h₁ q hq
    · exact h₂ q hq

omit [DecidableEq A] in
lemma inDup_of_unrestricted {S : Set A} {Q : SConstr A} (h : Q.Unrestricted) : Q.InDup S := by
  unfold Unrestricted at h
  intro q hq; simp [h] at hq

lemma inDup_omega_smul (S : Set A) (Q : SConstr A) : ((Mult.omega : Mult) • Q).InDup S :=
  inDup_of_unrestricted (unrestricted_omega_smul Q)

omit [DecidableEq A] in
lemma inDup_lin_iff {S : Set A} {Q : SConstr A} : Q.lin.InDup S ↔ Q.InDup S := Iff.rfl

omit [DecidableEq A] in
lemma inDup_atom_one_iff {S : Set A} {q : A} : (atom .one q).InDup S ↔ q ∈ S := by
  unfold InDup; simp

omit [DecidableEq A] in
lemma inDup_atom_omega (S : Set A) (q : A) : (atom .omega q).InDup S :=
  inDup_of_unrestricted rfl

lemma inDup_smul_iff {S : Set A} {p : Mult} {Q : SConstr A} :
    (p • Q).InDup S ↔ p = .omega ∨ Q.InDup S := by
  cases p
  · simp
  · simp [inDup_omega_smul]

/-- An induction principle for simple constraints: every simple constraint is obtained from
`ε` by adding scaled atomic constraints `ω · q` and `1 · q`. -/
theorem induction_on' {motive : SConstr A → Prop} (Q : SConstr A) (h0 : motive 0)
    (hω : ∀ q Q, motive Q → motive (atom .omega q + Q))
    (h1 : ∀ q Q, motive Q → motive (atom .one q + Q)) : motive Q := by
  obtain ⟨U, L⟩ := Q
  induction L using Multiset.induction_on with
  | empty =>
    induction U using Finset.induction_on with
    | empty => exact h0
    | insert a U _ ih =>
      have : (⟨insert a U, 0⟩ : SConstr A) = atom .omega a + ⟨U, 0⟩ := by
        ext x <;> simp
      rw [this]; exact hω _ _ ih
  | cons a L ih =>
    have : (⟨U, a ::ₘ L⟩ : SConstr A) = atom .one a + ⟨U, L⟩ := by
      ext x
      · simp
      · simp
    rw [this]; exact h1 _ _ ih

-- [NOT IN PAPER ◀ END] basic facts about simple constraints

end SConstr

end LQT
