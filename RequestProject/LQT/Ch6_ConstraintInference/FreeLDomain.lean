module

public import RequestProject.LQT.Ch6_ConstraintInference.FreeDomain
public import RequestProject.LQT.Ch5_QualifiedTypeSystem.Syntax

/-!
# A lawful family of domains (non-vacuity of `LDomain.Lawful`)

The stripped-down domain of §6.3.2 / Figure 10a (`freeDomain`) is stable under any mapping of atoms
which sends duplicable atoms to duplicable atoms (`freeEntails_map`).  Consequently, for every
family of sets of duplicable atoms closed under weakening, the levelwise free domains form a
lawful family of domains (`freeLDomain_lawful`).  In particular the hypothesis `D.Lawful` of
the main theorems is satisfiable.

Paper location: none.  The paper has no type-variable levels and does not check that its
domain satisfies the laws; this whole file is a non-vacuity check added by the formalization.
-/

@[expose] public section

namespace LQT

open SConstr

-- [NOT IN PAPER ▶ START] non-vacuity of `LDomain.Lawful` (whole file); builds on the domain of
--   §6.3.2, Figure 10a

section
variable {A B : Type*} [DecidableEq A] [DecidableEq B]

omit [DecidableEq A] in
lemma count_map_eq_card_filter (f : A → B) (s : Multiset A) (r : B) :
    (s.map f).count r = (s.filter (fun a => f a = r)).card := by
  rw [Multiset.count_map]
  congr 1
  exact Multiset.filter_congr (fun _ _ => eq_comm)

/-- Free entailment is stable under mapping atoms along a function preserving duplicability. -/
theorem freeEntails_map {S : Set A} {S' : Set B} (f : A → B) (hf : ∀ q ∈ S, f q ∈ S')
    {Q₁ Q₂ : SConstr A} (h : freeEntails S Q₁ Q₂) :
    freeEntails S' (Q₁.map f) (Q₂.map f) := by
  obtain ⟨hU, hN, hD⟩ := h
  refine ⟨Finset.image_subset_image hU, fun r hr => ?_, fun r hr hpos => ?_⟩
  · -- all preimages of `r` are non-duplicable
    have hpre : ∀ q, f q = r → q ∉ S := fun q hq hS => hr (hq ▸ hf q hS)
    have hle : Q₁.L.filter (fun a => f a = r) ≤ Q₂.L.filter (fun a => f a = r) := by
      rw [Multiset.le_iff_count]
      intro q
      simp only [Multiset.count_filter]
      split_ifs with hq
      · exact (hN q (hpre q hq)).1
      · exact le_rfl
    simp only [map_L, count_map_eq_card_filter]
    refine ⟨Multiset.card_le_card hle, fun hlt => ?_⟩
    have hne : ¬ Q₂.L.filter (fun a => f a = r) ≤ Q₁.L.filter (fun a => f a = r) := by
      intro h'
      have := Multiset.card_le_card h'
      omega
    rw [Multiset.le_iff_count] at hne
    push_neg at hne
    obtain ⟨q, hq⟩ := hne
    simp only [Multiset.count_filter] at hq
    split_ifs at hq with hfq
    · simp only [map_U, Finset.mem_image]
      exact ⟨q, (hN q (hpre q hfq)).2 hq, hfq⟩
    · omega
  · simp only [map_L, map_U, Finset.mem_image] at hpos ⊢
    obtain ⟨q, hq, rfl⟩ := Multiset.mem_map.mp (Multiset.count_pos.mp hpos)
    have hc : 0 < Q₂.L.count q := Multiset.count_pos.mpr hq
    have key : q ∈ Q₁.U ∨ 0 < Q₁.L.count q := by
      by_cases hS : q ∈ S
      · exact hD q hS hc
      · obtain ⟨h1, h2⟩ := hN q hS
        by_cases hlt : Q₁.L.count q < Q₂.L.count q
        · exact Or.inl (h2 hlt)
        · right; omega
    rcases key with h | h
    · exact Or.inl ⟨q, h, rfl⟩
    · right
      exact Multiset.count_pos.mpr (Multiset.mem_map_of_mem f (Multiset.count_pos.mp h))

end

variable {A : Nat → Type} [∀ k, DecidableEq (A k)] [Weakening A]

/-- The levelwise stripped-down domains, for a family `S` of sets of duplicable atoms. -/
def freeLDomain (S : (k : Nat) → Set (A k)) : LDomain A := fun k => freeDomain (S k)

/-- For any family of sets of duplicable atoms closed under weakening, the levelwise free
domains form a lawful family. -/
theorem freeLDomain_lawful (S : (k : Nat) → Set (A k))
    (hS : ∀ {k : Nat} (j : Nat) {q : A k}, q ∈ S k → Weakening.wk j q ∈ S (k + j)) :
    (freeLDomain S).Lawful where
  lawful k := freeDomain_lawful (S k)
  dup_wk j _ hq := hS j hq
  entails_wk j _ _ h := freeEntails_map (Weakening.wk j) (fun _ hq => hS j hq) h

/-- The concrete family of domains on atoms `P τ̄` in which an atom is duplicable exactly when
its predicate belongs to `Pdup` (for instance, a class of "unrestricted" predicates). -/
def predLDomain {P : Type} (Pdup : Set P) : LDomain (Atom P) :=
  freeLDomain (fun _ => {q | q.1 ∈ Pdup})

/-- The concrete family `predLDomain Pdup` is lawful; hence the hypothesis `D.Lawful` of the
main theorems is satisfiable for the polymorphic language. -/
theorem predLDomain_lawful {P : Type} (Pdup : Set P) : (predLDomain Pdup).Lawful :=
  freeLDomain_lawful _ (fun _ _ hq => hq)

-- [NOT IN PAPER ◀ END] non-vacuity of `LDomain.Lawful`

end LQT
