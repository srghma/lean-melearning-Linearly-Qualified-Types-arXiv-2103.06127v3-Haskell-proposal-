module

public import RequestProject.LQT.Ch5_QualifiedTypeSystem.SimpleConstraints

/-!
# Mapping over the atoms of a simple constraint

`Q.map f` applies `f` to every atomic constraint of `Q`.  It is used to rename and to
substitute type variables in constraints (`Q[τ̄/ā]` in the paper).

Paper location: none.  This whole file is formalization infrastructure with no counterpart in
the paper.
-/

@[expose] public section

namespace LQT

-- [NOT IN PAPER ▶ START] mapping over atoms (whole file); used to implement `Q[τ̄/ā]`

namespace SConstr

variable {A B C : Type*} [DecidableEq A] [DecidableEq B] [DecidableEq C]

/-- Apply `f` to all the atomic constraints of `Q`. -/
def map (f : A → B) (Q : SConstr A) : SConstr B := ⟨Q.U.image f, Q.L.map f⟩

omit [DecidableEq A] in
@[simp] lemma map_U (f : A → B) (Q : SConstr A) : (Q.map f).U = Q.U.image f := rfl
omit [DecidableEq A] in
@[simp] lemma map_L (f : A → B) (Q : SConstr A) : (Q.map f).L = Q.L.map f := rfl

omit [DecidableEq A] in
@[simp] lemma map_zero (f : A → B) : (0 : SConstr A).map f = 0 := by
  ext <;> simp

@[simp] lemma map_add (f : A → B) (Q₁ Q₂ : SConstr A) :
    (Q₁ + Q₂).map f = Q₁.map f + Q₂.map f := by
  ext <;> simp [Finset.image_union]

@[simp] lemma map_smul (f : A → B) (π : Mult) (Q : SConstr A) :
    (π • Q).map f = π • Q.map f := by
  cases π
  · rfl
  · ext x <;> simp [Finset.image_union, Multiset.toFinset_map]

omit [DecidableEq A] in
@[simp] lemma map_atom (f : A → B) (π : Mult) (q : A) : (atom π q).map f = atom π (f q) := by
  cases π <;> ext <;> simp [atom]

omit [DecidableEq A] in
lemma map_map (f : A → B) (g : B → C) (Q : SConstr A) : (Q.map f).map g = Q.map (g ∘ f) := by
  ext <;> simp [Finset.image_image]

lemma map_id' (Q : SConstr A) : Q.map (fun x => x) = Q := by
  ext <;> simp

omit [DecidableEq A] in
lemma map_congr {f g : A → B} (h : ∀ x, f x = g x) (Q : SConstr A) : Q.map f = Q.map g := by
  rw [show f = g from funext h]

lemma map_eq_zero_iff (f : A → B) (Q : SConstr A) : Q.map f = 0 ↔ Q = 0 := by
  constructor
  · intro h
    have hU := congrArg SConstr.U h
    have hL := congrArg SConstr.L h
    simp only [map_U, zero_U, Finset.image_eq_empty, map_L, zero_L, Multiset.map_eq_zero] at hU hL
    ext <;> simp [hU, hL]
  · rintro rfl; simp

omit [DecidableEq A] in
lemma map_inDup (f : A → B) {S : Set A} {S' : Set B} (hf : ∀ q ∈ S, f q ∈ S')
    {Q : SConstr A} (h : Q.InDup S) : (Q.map f).InDup S' := by
  intro q hq
  simp only [map_L, Multiset.mem_map] at hq
  obtain ⟨a, ha, rfl⟩ := hq
  exact hf a (h a ha)

/-- `map f` as an additive monoid homomorphism. -/
def mapHom (f : A → B) : SConstr A →+ SConstr B where
  toFun := map f
  map_zero' := map_zero f
  map_add' := map_add f

lemma map_sum {ι : Type*} (f : A → B) (s : Finset ι) (g : ι → SConstr A) :
    (∑ i ∈ s, g i).map f = ∑ i ∈ s, (g i).map f :=
  _root_.map_sum (mapHom f) g s

/-- For injective maps, mapping commutes with multiset difference. -/
lemma _root_.Multiset.map_tsub_of_injective (f : A → B) (hf : Function.Injective f)
    (s t : Multiset A) : (s - t).map f = s.map f - t.map f := by
  ext b
  by_cases h : ∃ a, f a = b
  · obtain ⟨a, rfl⟩ := h
    simp [Multiset.count_map_eq_count' f _ hf]
  · push_neg at h
    have hz : ∀ X : Multiset A, Multiset.count b (X.map f) = 0 := fun X =>
      Multiset.count_eq_zero.mpr (by simp; exact fun a _ => h a)
    rw [Multiset.count_sub, hz, hz, hz]

-- [NOT IN PAPER ◀ END] mapping over atoms

end SConstr

end LQT
