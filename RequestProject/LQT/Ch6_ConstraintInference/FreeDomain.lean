module

public import RequestProject.LQT.Ch5_QualifiedTypeSystem.EntailmentLemmas

/-!
# A concrete constraint domain (§6.3.2, Figure 10a)

Paper location: §6.3.2 "An atomic-constraint solver", Figure 10 "A stripped-down constraint
domain", sub-figure (a) "Entailment relation", and the remark of §5.1 that `1·q ⊩ ω·q` does
not hold (`freeDomain_not_one_entails_omega`).  The start and end of each part is marked by
`-- [PAPER ▶ START]` / `-- [PAPER ◀ END]` comments.

§6.3.2 of the paper offers "a stripped-down constraint domain" in which atomic
constraints are abstract: an atomic constraint is entailed only if it is assumed (respecting
linearity), except for the duplicable constraints of `𝒟` which can be duplicated and discarded.
We give a semantic description of this entailment relation, for an arbitrary set `𝒟`:

`(U₁, L₁) ⊩ (U₂, L₂)` iff
* `U₂ ⊆ U₁`;
* for every non-duplicable `q`, each linear copy of `q` in `L₁` is used exactly once: there
  are at least as many copies in `L₂`, and if there are strictly more then `q ∈ U₁`;
* for every duplicable `q`, if `q` occurs in `L₂` then `q ∈ U₁` or `q` occurs in `L₁`.

We prove that it satisfies the repaired laws (`freeDomain_lawful`) for every `𝒟`, and the
paper's laws when `𝒟 = ∅` (`freeDomain_paperLaws`); in particular neither set of laws is
vacuous.  We then use it to show that the paper's Lemma 5.5 fails for lawful domains as soon as
`𝒟` is non-empty (`paper_scaling_inv_fails`), and we check that the rules of Figure 10a are
valid in it.
-/

@[expose] public section

namespace LQT

open SConstr

variable {A : Type*} [DecidableEq A]

-- [PAPER ▶ START] §6.3.2 › Figure 10 "A stripped-down constraint domain", (a) "Entailment
--   relation": the domain itself, described semantically (the paper gives it by the rules Q_Hyp,
--   Q_Prod, Q_Empty, Q_DiscardD, Q_DupD, checked at the end of this file), generalised from `𝒟 =
--   {𝓛}` to any set `𝒟`
/-- The entailment relation of the stripped-down constraint domain. -/
def freeEntails (S : Set A) (Q₁ Q₂ : SConstr A) : Prop :=
  Q₂.U ⊆ Q₁.U ∧
  (∀ q, q ∉ S → Q₁.L.count q ≤ Q₂.L.count q ∧ (Q₁.L.count q < Q₂.L.count q → q ∈ Q₁.U)) ∧
  (∀ q, q ∈ S → 0 < Q₂.L.count q → q ∈ Q₁.U ∨ 0 < Q₁.L.count q)

/-- The stripped-down constraint domain with duplicable constraints `𝒟 = S`. -/
def freeDomain (S : Set A) : Domain A := ⟨freeEntails S, S⟩

-- [PAPER ◀ END] §6.3.2 › Figure 10a (definition of the domain)

-- [NOT IN PAPER ▶ START] the stripped-down domain satisfies the laws: the paper does not check
--   this; it shows that the hypotheses of the main theorems are satisfiable
section
open Classical

lemma free_tensor_inv (S : Set A) {Q Q₁ Q₂ : SConstr A} (h : freeEntails S Q (Q₁ + Q₂)) :
    ∃ Q' QD Q'', QD.InDup S ∧ Q = Q' + QD + Q'' ∧ freeEntails S (Q' + QD) Q₁ ∧
      freeEntails S (QD + Q'') Q₂ := by
  obtain ⟨hU, hN, hD⟩ := h
  set N := Q.L.filter (fun q => q ∉ S) with hNdef
  set N₁ := N ∩ Q₁.L with hN₁def
  have cN : ∀ q, N.count q = if q ∈ S then 0 else Q.L.count q := by
    intro q; rw [hNdef, Multiset.count_filter]; split_ifs <;> simp_all
  have cP : ∀ q, (Q.L.filter (fun q => q ∈ S)).count q = if q ∈ S then Q.L.count q else 0 := by
    intro q; rw [Multiset.count_filter]
  have cN₁ : ∀ q, N₁.count q = min (N.count q) (Q₁.L.count q) := by
    intro q; rw [hN₁def, Multiset.count_inter]
  have hle : N₁ ≤ N := Multiset.inter_le_left
  have cS : ∀ q, (N - N₁).count q = N.count q - N₁.count q := fun q => Multiset.count_sub _ _ _
  refine ⟨⟨∅, N₁⟩, ⟨Q.U, Q.L.filter (fun q => q ∈ S)⟩, ⟨∅, N - N₁⟩, ?_, ?_, ?_, ?_⟩
  · intro q hq; exact (Multiset.mem_filter.mp hq).2
  · ext x
    · simp
    · simp only [add_L, Multiset.count_add, cS, cN₁, cN, cP]
      split_ifs <;> omega
  · refine ⟨fun x hx => ?_, ?_, ?_⟩
    · have := hU (Finset.mem_union_left _ hx)
      simpa using this
    · intro q hq
      have := hN q hq
      simp only [add_L, Multiset.count_add, cN₁, cN, cP, hq, if_false, add_U,
        Finset.empty_union] at this ⊢
      refine ⟨by omega, fun hlt => this.2 (by omega)⟩
    · intro q hq hpos
      have := hD q hq (by simp only [add_L, Multiset.count_add]; omega)
      simp only [add_L, Multiset.count_add, cN₁, cN, cP, hq, if_true, add_U,
        Finset.empty_union] at this ⊢
      rcases this with h | h
      · exact Or.inl h
      · right; omega
  · refine ⟨fun x hx => ?_, ?_, ?_⟩
    · have := hU (Finset.mem_union_right _ hx)
      simpa using this
    · intro q hq
      have := hN q hq
      simp only [add_L, Multiset.count_add, cS, cN₁, cN, cP, hq, if_false, add_U,
        Finset.union_empty] at this ⊢
      refine ⟨by omega, fun hlt => this.2 (by omega)⟩
    · intro q hq hpos
      have := hD q hq (by simp only [add_L, Multiset.count_add]; omega)
      simp only [add_L, Multiset.count_add, cS, cN₁, cN, cP, hq, if_true, add_U,
        Finset.union_empty] at this ⊢
      rcases this with h | h
      · exact Or.inl h
      · right; omega

end

/-- The stripped-down constraint domain satisfies the repaired laws, for every `𝒟`. -/
theorem freeDomain_lawful (S : Set A) : (freeDomain S).Lawful where
  refl Q := ⟨subset_refl _, fun q _ => ⟨le_refl _, fun h => absurd h (lt_irrefl _)⟩,
    fun q _ h => Or.inr h⟩
  cut := by
    intro Q Q₁ Q₂ Q₃ h₁ h₂
    obtain ⟨a1, b1, c1⟩ := h₁
    obtain ⟨a2, b2, c2⟩ := h₂
    refine ⟨?_, ?_, ?_⟩
    · intro x hx
      have := a2 hx
      simp only [add_U, Finset.mem_union] at this ⊢
      rcases this with h | h
      · exact Or.inl h
      · exact Or.inr (a1 h)
    · intro q hq
      have k1 := b1 q hq
      have k2 := b2 q hq
      simp only [add_L, Multiset.count_add, add_U, Finset.mem_union] at k2 ⊢
      refine ⟨by omega, fun hlt => ?_⟩
      by_cases h : Q.L.count q + Q₂.L.count q < Q₃.L.count q
      · rcases k2.2 h with h' | h'
        · exact Or.inl h'
        · exact Or.inr (a1 h')
      · exact Or.inr (k1.2 (by omega))
    · intro q hq hpos
      have k2 := c2 q hq hpos
      simp only [add_L, Multiset.count_add, add_U, Finset.mem_union] at k2 ⊢
      rcases k2 with (h | h) | h
      · exact Or.inl (Or.inl h)
      · exact Or.inl (Or.inr (a1 h))
      · by_cases h' : 0 < Q.L.count q
        · exact Or.inr (by omega)
        · rcases c1 q hq (by omega) with h'' | h''
          · exact Or.inl (Or.inr h'')
          · exact Or.inr (by omega)
  tensor_inv h := free_tensor_inv S h
  empty_inv := by
    intro Q h q hq
    by_contra hS
    have := (h.2.1 q hS).1
    simp only [zero_L, Multiset.count_zero] at this
    exact absurd (Multiset.count_pos.mpr hq) (by omega)
  tensor := by
    intro Q₁ Q₁' Q₂ Q₂' h₁ h₂
    obtain ⟨a1, b1, c1⟩ := h₁
    obtain ⟨a2, b2, c2⟩ := h₂
    refine ⟨Finset.union_subset_union a1 a2, ?_, ?_⟩
    · intro q hq
      have k1 := b1 q hq
      have k2 := b2 q hq
      simp only [add_L, Multiset.count_add, add_U, Finset.mem_union]
      refine ⟨by omega, fun hlt => ?_⟩
      by_cases h : Q₁.L.count q < Q₁'.L.count q
      · exact Or.inl (k1.2 h)
      · exact Or.inr (k2.2 (by omega))
    · intro q hq hpos
      simp only [add_L, Multiset.count_add, add_U, Finset.mem_union] at hpos ⊢
      by_cases h : 0 < Q₁'.L.count q
      · rcases c1 q hq h with h' | h'
        · exact Or.inl (Or.inl h')
        · exact Or.inr (by omega)
      · rcases c2 q hq (by omega) with h' | h'
        · exact Or.inl (Or.inr h')
        · exact Or.inr (by omega)
  scale_atom := by
    intro Q ρ q π h
    obtain ⟨a, b, c⟩ := h
    cases π with
    | one => exact ⟨a, b, c⟩
    | omega =>
      have hq : q ∈ Q.U ∪ Q.L.toFinset := by
        cases ρ with
        | omega => exact Finset.mem_union_left _ (a (by simp [atom]))
        | one =>
          by_cases hS : q ∈ S
          · rcases c q hS (by simp [atom]) with h | h
            · exact Finset.mem_union_left _ h
            · exact Finset.mem_union_right _ (Multiset.mem_toFinset.mpr (Multiset.count_pos.mp h))
          · have := b q hS
            by_cases h' : Q.L.count q < 1
            · exact Finset.mem_union_left _ (this.2 (by simpa [atom] using h'))
            · exact Finset.mem_union_right _
                (Multiset.mem_toFinset.mpr (Multiset.count_pos.mp (by omega)))
      refine ⟨?_, ?_, ?_⟩
      · intro x hx
        simp only [Mult.omega_mul, atom_omega_U, Finset.mem_singleton] at hx
        subst hx; exact hq
      · intro q' _
        simp [atom]
      · intro q' _ hpos
        simp [atom] at hpos
  derelict := by
    intro Q₁ Q₂ h
    obtain ⟨a, b, c⟩ := h
    refine ⟨fun x hx => Finset.mem_union_left _ (a hx), ?_, ?_⟩
    · intro q hq
      refine ⟨by simp, fun hlt => ?_⟩
      simp only [omega_smul_L, Multiset.count_zero, omega_smul_U, Finset.mem_union,
        Multiset.mem_toFinset] at hlt ⊢
      by_cases h : Q₁.L.count q < Q₂.L.count q
      · exact Or.inl ((b q hq).2 h)
      · exact Or.inr (Multiset.count_pos.mp (by omega))
    · intro q hq hpos
      rcases c q hq hpos with h | h
      · exact Or.inl (Finset.mem_union_left _ h)
      · exact Or.inl (Finset.mem_union_right _ (Multiset.mem_toFinset.mpr
          (Multiset.count_pos.mp h)))
  weaken := by
    intro Q₁ Q₂ Q' h
    obtain ⟨a, b, c⟩ := h
    refine ⟨fun x hx => Finset.mem_union_right _ (a hx), ?_, ?_⟩
    · intro q hq
      have := b q hq
      simp only [add_L, omega_smul_L, zero_add, add_U, Finset.mem_union]
      exact ⟨this.1, fun h => Or.inr (this.2 h)⟩
    · intro q hq hpos
      simp only [add_L, omega_smul_L, zero_add, add_U, Finset.mem_union]
      rcases c q hq hpos with h | h
      · exact Or.inl (Or.inr h)
      · exact Or.inr h
  dup := by
    intro q hq
    refine ⟨by simp, ?_, ?_⟩
    · intro q' hq'
      have : q' ≠ q := fun h => hq' (h ▸ hq)
      simp [atom, this]
    · intro q' _ hpos
      right
      simp only [add_L, atom_one_L, Multiset.count_add, Multiset.count_singleton] at hpos ⊢
      split_ifs at hpos ⊢ <;> omega
  discard := by
    intro q hq
    refine ⟨by simp, ?_, ?_⟩
    · intro q' hq'
      have : q' ≠ q := fun h => hq' (h ▸ hq)
      simp [atom, this]
    · intro q' _ hpos
      simp at hpos
  dup_closed := by
    intro Q Q' hQ h q hq
    by_contra hS
    have := (h.2.1 q hS).1
    have h0 : Q.L.count q = 0 := Multiset.count_eq_zero.mpr (fun hm => hS (hQ q hm))
    have := Multiset.count_pos.mpr hq
    omega
  scale_atom_inv := by
    intro Q π ρ q h
    cases π with
    | one => exact ⟨Q, 0, inDup_zero _, by simp, h⟩
    | omega =>
      obtain ⟨a, b, c⟩ := h
      have hqU : q ∈ Q.U := a (by simp [atom])
      refine ⟨Q.unr, Q.lin, ?_, ?_, ?_⟩
      · intro x hx
        by_contra hS
        have := (b x hS).1
        simp only [Mult.omega_mul, atom_omega_L, Multiset.count_zero] at this
        have h2 : 0 < Q.L.count x := Multiset.count_pos.mpr hx
        omega
      · rw [omega_smul_unr]; exact unr_add_lin Q
      · cases ρ with
        | omega =>
          refine ⟨fun x hx => by simp at hx; subst hx; exact hqU, ?_, ?_⟩
          · intro q' _; simp [atom]
          · intro q' _ hpos; simp [atom] at hpos
        | one =>
          refine ⟨by simp, ?_, ?_⟩
          · intro q' _
            refine ⟨by simp, fun hlt => ?_⟩
            simp only [atom_one_L, Multiset.count_singleton, unr_L, Multiset.count_zero] at hlt
            split_ifs at hlt with hh
            · subst hh; exact hqU
            · omega
          · intro q' _ hpos
            simp only [atom_one_L, Multiset.count_singleton] at hpos
            split_ifs at hpos with hh
            · subst hh; exact Or.inl hqU
            · omega

/-- With `𝒟 = ∅` the stripped-down domain satisfies the laws of Figure 4 verbatim. -/
theorem freeDomain_paperLaws : (freeDomain (∅ : Set A)).PaperLaws where
  toCommonLaws := (freeDomain_lawful ∅).toCommonLaws
  scale_atom_inv := by
    intro Q π ρ q h
    obtain ⟨Q', QD, hQD, rfl, h'⟩ := (freeDomain_lawful ∅).scale_atom_inv h
    have hU : QD.Unrestricted := by
      unfold Unrestricted
      rw [Multiset.eq_zero_iff_forall_notMem]
      intro x hx; exact hQD x hx
    refine ⟨Q' + QD, ?_, (freeDomain_lawful ∅).weaken_dup hQD h'⟩
    cases π with
    | one => rfl
    | omega => rw [smul_add, omega_smul_of_unrestricted hU]

-- [NOT IN PAPER ◀ END] the stripped-down domain satisfies the laws

-- [NOT IN PAPER ▶ START] counterexample to Lemma 5.5 (§5.1) as stated, when `𝒟` is non-empty
/-- The paper's Lemma 5.5 (inversion of scaling, without the duplicable part `Q_𝒟`) fails in
the lawful stripped-down domain as soon as `𝒟` is non-empty: `1 · q ⊩ ω · ε` for `q ∈ 𝒟`,
but `1 · q` is not of the form `ω · Q'`. -/
theorem paper_scaling_inv_fails {S : Set A} {q : A} (hq : q ∈ S) :
    (freeDomain S).Entails (atom .one q) ((Mult.omega : Mult) • 0) ∧
      ¬ ∃ Q', atom .one q = (Mult.omega : Mult) • Q' := by
  refine ⟨?_, ?_⟩
  · rw [smul_zero]; exact (freeDomain_lawful S).discard hq
  · rintro ⟨Q', h⟩
    have := congrArg SConstr.L h
    simp at this

-- [NOT IN PAPER ◀ END] counterexample to Lemma 5.5

-- [PAPER ▶ START] §6.3.2 › Figure 10a "Entailment relation": rules Q_Hyp, Q_Prod, Q_Empty,
--   Q_DiscardD, Q_DupD
/-! ### The rules of Figure 10a are valid in the stripped-down domain -/

section Fig10a

variable (S : Set A)

/-- Rule Q_Hyp: `ω · Q ⊗ π · q ⊩ π · q`. -/
theorem fig10a_hyp (Q : SConstr A) (π : Mult) (q : A) :
    (freeDomain S).Entails ((Mult.omega : Mult) • Q + atom π q) (atom π q) :=
  (freeDomain_lawful S).weaken Q ((freeDomain_lawful S).refl _)

/-- Rule Q_Prod. -/
theorem fig10a_prod {Q₁ Q₁' Q₂ Q₂' : SConstr A} (h₁ : (freeDomain S).Entails Q₁ Q₁')
    (h₂ : (freeDomain S).Entails Q₂ Q₂') : (freeDomain S).Entails (Q₁ + Q₂) (Q₁' + Q₂') :=
  (freeDomain_lawful S).tensor h₁ h₂

/-- Rule Q_Empty: `ω · Q ⊩ ε`. -/
theorem fig10a_empty (Q : SConstr A) : (freeDomain S).Entails ((Mult.omega : Mult) • Q) 0 := by
  have := (freeDomain_lawful S).weaken Q ((freeDomain_lawful S).refl 0)
  rwa [add_zero] at this

/-- Rule Q_DiscardD: `1 · 𝓛 ⊩ ε` for a duplicable `𝓛`. -/
theorem fig10a_discardD {l : A} (hl : l ∈ S) : (freeDomain S).Entails (atom .one l) 0 :=
  (freeDomain_lawful S).discard hl

/-- Rule Q_DupD: `1 · 𝓛 ⊩ 1 · 𝓛 ⊗ 1 · 𝓛` for a duplicable `𝓛`. -/
theorem fig10a_dupD {l : A} (hl : l ∈ S) :
    (freeDomain S).Entails (atom .one l) (atom .one l + atom .one l) :=
  (freeDomain_lawful S).dup hl

end Fig10a

-- [PAPER ◀ END] §6.3.2 › Figure 10a (rules)

-- [PAPER ▶ START] §5.1, remark after Figure 4: "Crucially, it is not the case that `1·q ⊩ ω·q`
--   for `q ∈ 𝒟`" (see also `Domain.Lawful.one_entails_omega`)

/-- In the stripped-down domain of Figure 10a, `1·q ⊩ ω·q` never holds, even for `q ∈ 𝒟`. -/
theorem freeDomain_not_one_entails_omega (S : Set A) (q : A) :
    ¬ (freeDomain S).Entails (SConstr.atom .one q) (SConstr.atom .omega q) := by
  intro h
  have := h.1 (by simp : q ∈ (SConstr.atom .omega q : SConstr A).U)
  simp at this

-- [PAPER ◀ END] §5.1, `1·q ⊮ ω·q` in the domain of Figure 10a

end LQT
