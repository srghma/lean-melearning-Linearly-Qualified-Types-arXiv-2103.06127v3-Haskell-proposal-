module

public import RequestProject.LQT.Ch6_ConstraintInference.Generation

/-!
# Constraint solving (§6.3, Figure 9)

Paper location: §6.3 "Constraint solving" (the atomic-solver judgement, Lemma 6.5 "Constraint
solver soundness", Property 6.6 "Atomic-constraint solver soundness") and §6.3.1 "Constraint
solver algorithm" (Figure 9 "Constraint solver").  The atomic solver of Figure 10b (§6.3.2) is
in `AtomicSolver.lean`.  The start and end of each part is marked by
`-- [PAPER ▶ START]` / `-- [PAPER ◀ END]` comments.

The constraint solver `U ; D ; Lᵢ ⊢s C ⇝ Lₒ` (rules S_Atom, S_Mult, S_ImplOne, S_Add,
S_ImplMany) is parameterised by an atomic-constraint solver `U ; D ; Lᵢ ⊢simp π·q ⇝ Lₒ`.
Figure 9 has no rule for a simple wanted constraint other than a single atom `π·q`: the paper
implicitly regards a simple constraint `(U, L)` as the multiplicative conjunction of its atoms.
Since constraint generation emits `ε` (for data constructors and for variables with an
unqualified type) and composite simple constraints (e.g. the constraint of an existential
type), we make this convention explicit with two extra rules, S_Empty (`ε` consumes nothing)
and S_Split (`Q₁ ⊗ Q₂` is solved like `C₁ ⊗ C₂` in S_Mult); Lemma 6.5 covers them.
The linear contexts are lists; the linear part of the assumption of an implication is a
multiset, which is added to the front of the lists in any order.

**About Property 6.6.**  The paper requires of the atomic solver that `Lₒ ⊆ Lᵢ` and
`(U, D ⊎ Lᵢ) ⊩ π·q ⊗ (∅, Lₒ)` (`AtomSolver.PaperSound`).  With only this hypothesis, the
S_ImplOne case of the paper's proof of Lemma 6.5 does not go through: it needs to cancel
`(∅, Lₒ)` from both sides of an entailment, which the laws of Figure 4 do not allow.  We
therefore require the (stronger, and natural) property that the consumed assumptions entail
the atom: `Lₒ ⊆ Lᵢ` and `(U, D ⊎ (Lᵢ ∖ Lₒ)) ⊩ π·q` (`AtomSolver.Sound`), which implies the
paper's property (`AtomSolver.Sound.paperSound`), and which the atomic solver of Figure 10b
satisfies (`simpleSolver_sound`).  We then prove Lemma 6.5 both in this strengthened form and
in the paper's form.
-/

@[expose] public section

namespace LQT

open SConstr

section
variable {A : Type*} [DecidableEq A]

-- [PAPER ▶ START] §6.3: the atomic-constraint solver judgement `U ; D ; Lᵢ ⊢simp π·q ⇝ Lₒ` (a
--   parameter of the solver)
/-- An atomic-constraint solver: a relation `U ; D ; Lᵢ ⊢simp π·q ⇝ Lₒ`, presented as a
predicate on `U D Lᵢ π q Lₒ`. -/
def AtomSolver (A : Type*) := Finset A → List A → List A → Mult → A → List A → Prop

-- [PAPER ◀ END] §6.3, atomic-constraint solver judgement

namespace AtomSolver

-- [PAPER ▶ START] §6.3 › Property 6.6 "Atomic-constraint solver soundness", as stated in the paper
/-- Property 6.6 (atomic-constraint solver soundness) as stated in the paper (for duplicable
contexts `D`, the only ones the solver ever builds). -/
def PaperSound (D : Domain A) (S : AtomSolver A) : Prop :=
  ∀ U Dl Li π q Lo, (∀ x ∈ Dl, x ∈ D.Dup) → S U Dl Li π q Lo →
    (Lo : Multiset A) ≤ Li ∧ D.Entails ⟨U, (Dl : Multiset A) + Li⟩ (atom π q + ⟨∅, Lo⟩)

-- [PAPER ◀ END] §6.3 › Property 6.6

-- [NOT IN PAPER ▶ START] strengthened atomic-solver soundness (deviation from Property 6.6, see the
--   file header), helpers, and the proof that it implies Property 6.6
/-- Strengthened atomic-solver soundness: the consumed assumptions entail the atom. -/
def Sound (D : Domain A) (S : AtomSolver A) : Prop :=
  ∀ U Dl Li π q Lo, (∀ x ∈ Dl, x ∈ D.Dup) → S U Dl Li π q Lo →
    (Lo : Multiset A) ≤ Li ∧ D.Entails ⟨U, (Dl : Multiset A) + ((Li : Multiset A) - Lo)⟩ (atom π q)

/-- Splitting a context `(U, D ⊎ L)` off a linear part `Lₒ ≤ L`. -/
lemma ctx_split (U : Finset A) (Dl Li Lo : Multiset A) (h : Lo ≤ Li) :
    (⟨U, Dl + Li⟩ : SConstr A) = ⟨U, Dl + (Li - Lo)⟩ + ⟨∅, Lo⟩ := by
  ext x
  · simp
  · simp only [add_L]
    rw [add_assoc, tsub_add_cancel_of_le h]

lemma ctx_dup_split (U : Finset A) (Dl : Multiset A) (X : Multiset A) :
    (⟨U, Dl + X⟩ : SConstr A) = ⟨∅, Dl⟩ + ⟨U, X⟩ := by
  ext x <;> simp

omit [DecidableEq A] in
/-- Splitting a list according to a predicate, at the level of multisets. -/
lemma filter_split (S : Set A) [DecidablePred (· ∈ S)] (l : List A) :
    ((l.filter (fun x => decide (x ∈ S)) : List A) : Multiset A) +
      ((l.filter (fun x => decide (x ∉ S)) : List A) : Multiset A) = l := by
  rw [Multiset.coe_add]
  apply Multiset.coe_eq_coe.mpr
  have : (fun x => decide (x ∉ S)) = (fun x => !decide (x ∈ S)) := by funext x; simp
  rw [this]
  exact List.filter_append_perm _ _

/-- The strengthened property implies the paper's Property 6.6. -/
theorem Sound.paperSound {D : Domain A} (hD : D.Lawful) {S : AtomSolver A} (hS : S.Sound D) :
    S.PaperSound D := by
  intro U Dl Li π q Lo hDl h
  obtain ⟨hle, hent⟩ := hS U Dl Li π q Lo hDl h
  refine ⟨hle, ?_⟩
  rw [ctx_split U Dl Li Lo hle]
  exact hD.tensor hent (hD.refl _)

-- [NOT IN PAPER ◀ END] strengthened atomic-solver soundness

end AtomSolver

end

section Leveled

variable {A : Nat → Type} [∀ k, DecidableEq (A k)] [Weakening A]

-- [PAPER ▶ START] §6.3.1 › Figure 9 "Constraint solver": rules S_Atom, S_Mult, S_ImplOne, S_Add,
--   S_ImplMany (one constructor per rule)
open Classical in
/-- The constraint solver `U ; D ; Lᵢ ⊢s C ⇝ Lₒ` (Figure 9, rules S_*), with `k` type variables
in scope, parameterised by an atomic-constraint solver `S k` for each `k`.  When solving an
implication `π·∀ā.(Q₀ ⊸ C)` the contexts are weakened under the bound type variables `ā`; in
rule S_ImplOne the output of the inner problem must consist of weakened outer assumptions (the
inner linear assumptions must all be consumed, as in the paper's side condition `Lₒ ⊆ Lᵢ`). -/
inductive Solve (D : LDomain A) (S : (k : Nat) → AtomSolver (A k)) :
    {k : Nat} → Finset (A k) → List (A k) → List (A k) → Wanted A k → List (A k) → Prop
  /-- S_Atom -/
  | atom {k} {U : Finset (A k)} {Dl Li : List (A k)} {π : Mult} {q : A k} {Lo : List (A k)} : S k U Dl Li π q Lo → Solve D S U Dl Li (.simple (atom π q)) Lo
  /-- S_Mult -/
  | mult {k} {U : Finset (A k)} {Dl Li Lo' Lo : List (A k)} {C₁ C₂ : Wanted A k} : Solve D S U Dl Li C₁ Lo' →
      Solve D S U Dl Lo' C₂ Lo → Solve D S U Dl Li (.tensor C₁ C₂) Lo
  /-- S_Add -/
  | add {k} {U : Finset (A k)} {Dl Li Lo : List (A k)} {C₁ C₂ : Wanted A k} : Solve D S U Dl Li C₁ Lo → Solve D S U Dl Li C₂ Lo →
      Solve D S U Dl Li (.amp C₁ C₂) Lo
  /-- S_ImplOne: the linear assumptions `L₀` (listed in some order `l₀`) are split according to
  membership in `𝒟` and added to the front of the (weakened) contexts. -/
  | implOne {k j} {U : Finset (A k)} {Dl Li Lo : List (A k)} {Q₀ : SConstr (A (k + j))} {C : Wanted A (k + j)}
      (l₀ : List (A (k + j))) :
      (l₀ : Multiset (A (k + j))) = Q₀.L →
      Solve D S (U.image (Weakening.wk j) ∪ Q₀.U)
        (l₀.filter (fun x => decide (x ∈ (D (k + j)).Dup)) ++ Dl.map (Weakening.wk j))
        (l₀.filter (fun x => decide (x ∉ (D (k + j)).Dup)) ++ Li.map (Weakening.wk j)) C
        (Lo.map (Weakening.wk j)) →
      (Lo : Multiset (A k)) ≤ Li →
      Solve D S U Dl Li (.impl .one j Q₀ C) Lo
  /-- S_ImplMany -/
  | implMany {k j} {U : Finset (A k)} {Dl Li : List (A k)} {Q₀ : SConstr (A (k + j))} {C : Wanted A (k + j)}
      (l₀ : List (A (k + j))) :
      (l₀ : Multiset (A (k + j))) = Q₀.L →
      Solve D S (U.image (Weakening.wk j) ∪ Q₀.U)
        (l₀.filter (fun x => decide (x ∈ (D (k + j)).Dup)))
        (l₀.filter (fun x => decide (x ∉ (D (k + j)).Dup))) C [] →
      Solve D S U Dl Li (.impl .omega j Q₀ C) Li
  -- (no rule in Figure 9: the paper treats a simple wanted constraint `(U, L)` as the
  --   multiplicative conjunction of its atoms; the next two rules make this explicit)
  /-- S_Empty (implicit in the paper): the empty constraint `ε` consumes nothing. -/
  | empty {k} {U : Finset (A k)} {Dl Li : List (A k)} : Solve D S U Dl Li (.simple 0) Li
  /-- S_Split (implicit in the paper): a simple constraint `Q₁ ⊗ Q₂` is solved as the
  multiplicative conjunction of `Q₁` and `Q₂` (as in S_Mult). -/
  | split {k} {U : Finset (A k)} {Dl Li Lo' Lo : List (A k)} {Q₁ Q₂ : SConstr (A k)} :
      Solve D S U Dl Li (.simple Q₁) Lo' → Solve D S U Dl Lo' (.simple Q₂) Lo →
      Solve D S U Dl Li (.simple (Q₁ + Q₂)) Lo

-- [PAPER ◀ END] §6.3.1 › Figure 9

namespace LDomain.Lawful

variable {D : LDomain A} (hD : D.Lawful)
include hD

-- [PAPER ▶ START] §6.3 › Lemma 6.5 "Constraint solver soundness", strengthened form (proof:
--   Appendix B.6)
/-- **Lemma 6.5 (Constraint solver soundness)**, strengthened form: if
`U ; D ; Lᵢ ⊢s C ⇝ Lₒ` (with `D` duplicable) then `Lₒ ⊆ Lᵢ` and the consumed assumptions
`(U, D ⊎ (Lᵢ ∖ Lₒ))` entail `C`. -/
theorem solve_sound_strong {S : (k : Nat) → AtomSolver (A k)} (hS : ∀ k, (S k).Sound (D k))
    {k : Nat} {U : Finset (A k)} {Dl Li Lo : List (A k)} {C : Wanted A k}
    (h : Solve D S U Dl Li C Lo) (hDl : ∀ x ∈ Dl, x ∈ (D k).Dup) :
    (Lo : Multiset (A k)) ≤ Li ∧
      D.WEntails ⟨U, (Dl : Multiset (A k)) + ((Li : Multiset (A k)) - Lo)⟩ C := by
  classical
  induction h with
  | atom hs =>
    obtain ⟨hle, hent⟩ := hS _ _ _ _ _ _ _ hDl hs
    exact ⟨hle, (hD.wentails_simple_iff).mpr hent⟩
  | @mult k U Dl Li Lo' Lo C₁ C₂ _ _ ih₁ ih₂ =>
    have hk := hD.lawful k
    obtain ⟨hle₁, h₁⟩ := ih₁ hDl
    obtain ⟨hle₂, h₂⟩ := ih₂ hDl
    refine ⟨hle₂.trans hle₁, .dom ?_ (.tensor h₁ h₂)⟩
    have hDup : (⟨∅, (Dl : Multiset (A k))⟩ : SConstr (A k)).InDup (D k).Dup :=
      fun x hx => hDl x hx
    have e1 : ((Li : Multiset (A k)) - Lo) =
        ((Li : Multiset (A k)) - Lo') + ((Lo' : Multiset (A k)) - Lo) :=
      (tsub_add_tsub_cancel hle₁ hle₂).symm
    have e2 : (⟨U, (Dl : Multiset (A k)) + ((Li : Multiset (A k)) - Lo')⟩ : SConstr (A k)) +
        ⟨U, (Dl : Multiset (A k)) + ((Lo' : Multiset (A k)) - Lo)⟩ =
        (⟨∅, Dl⟩ + ⟨∅, Dl⟩) +
          ⟨U, ((Li : Multiset (A k)) - Lo') + ((Lo' : Multiset (A k)) - Lo)⟩ := by
      apply SConstr.ext
      · simp
      · simp only [add_L]; exact add_add_add_comm _ _ _ _
    rw [e1, e2, AtomSolver.ctx_dup_split]
    exact hk.tensor (hk.dup_dup hDup) (hk.refl _)
  | add _ _ ih₁ ih₂ =>
    obtain ⟨hle, h₁⟩ := ih₁ hDl
    obtain ⟨-, h₂⟩ := ih₂ hDl
    exact ⟨hle, .amp h₁ h₂⟩
  | @implOne k j U Dl Li Lo Q₀ C l₀ hl₀ _ hle ih =>
    have hDl' : ∀ x ∈ l₀.filter (fun x => decide (x ∈ (D (k + j)).Dup)) ++
        Dl.map (Weakening.wk j), x ∈ (D (k + j)).Dup := by
      intro x hx
      rcases List.mem_append.mp hx with h | h
      · simpa using (List.mem_filter.mp h).2
      · obtain ⟨y, hy, rfl⟩ := List.mem_map.mp h
        exact hD.dup_wk j (hDl y hy)
    obtain ⟨-, h⟩ := ih hDl'
    refine ⟨hle, ?_⟩
    have hsplit : ((l₀.filter (fun x => decide (x ∈ (D (k + j)).Dup)) : List _) :
        Multiset (A (k + j))) + ((l₀.filter (fun x => decide (x ∉ (D (k + j)).Dup)) : List _) :
          Multiset (A (k + j))) = Q₀.L := by
      rw [← hl₀]; exact AtomSolver.filter_split _ _
    have hmap : ((Li.map (Weakening.wk j) : List _) : Multiset (A (k + j))) -
        ((Lo.map (Weakening.wk j) : List _) : Multiset (A (k + j))) =
        ((Li : Multiset (A k)) - Lo).map (Weakening.wk j) := by
      rw [← Multiset.map_coe, ← Multiset.map_coe]
      conv_lhs => rw [← tsub_add_cancel_of_le hle, Multiset.map_add]
      exact add_tsub_cancel_right _ _
    have hle' : ((Lo.map (Weakening.wk j) : List _) : Multiset (A (k + j))) ≤
        ((Li.map (Weakening.wk j) : List _) : Multiset (A (k + j))) := by
      rw [← Multiset.map_coe, ← Multiset.map_coe]; exact Multiset.map_le_map hle
    have e : (⟨U.image (Weakening.wk j) ∪ Q₀.U,
        ((l₀.filter (fun x => decide (x ∈ (D (k + j)).Dup)) ++ Dl.map (Weakening.wk j) :
          List _) : Multiset (A (k + j))) +
        (((l₀.filter (fun x => decide (x ∉ (D (k + j)).Dup)) ++ Li.map (Weakening.wk j) :
          List _) : Multiset (A (k + j))) - ((Lo.map (Weakening.wk j) : List _) : Multiset _))⟩ :
          SConstr (A (k + j))) =
        (⟨U, (Dl : Multiset (A k)) + ((Li : Multiset (A k)) - Lo)⟩ : SConstr (A k)).wk j + Q₀ := by
      apply SConstr.ext
      · simp [SConstr.wk]
      · simp only [SConstr.wk, add_L, map_L, ← Multiset.coe_add]
        rw [add_tsub_assoc_of_le hle', hmap, ← hsplit, Multiset.map_add, ← Multiset.map_coe]
        generalize ((Li : Multiset (A k)) - Lo).map (Weakening.wk j) = X
        abel
    rw [e] at h
    simpa using WEntails.impl (D := D) Mult.one h
  | @implMany k j U Dl Li Q₀ C l₀ hl₀ _ ih =>
    have hk := hD.lawful k
    have hDl' : ∀ x ∈ l₀.filter (fun x => decide (x ∈ (D (k + j)).Dup)), x ∈ (D (k + j)).Dup := by
      intro x hx; simpa using (List.mem_filter.mp hx).2
    obtain ⟨-, h⟩ := ih hDl'
    refine ⟨le_refl _, ?_⟩
    have e : (⟨U.image (Weakening.wk j) ∪ Q₀.U,
        ((l₀.filter (fun x => decide (x ∈ (D (k + j)).Dup)) : List _) : Multiset (A (k + j))) +
        (((l₀.filter (fun x => decide (x ∉ (D (k + j)).Dup)) : List _) : Multiset _) -
          (([] : List (A (k + j))) : Multiset _))⟩ : SConstr (A (k + j))) =
        (⟨U, 0⟩ : SConstr (A k)).wk j + Q₀ := by
      have hsplit : ((l₀.filter (fun x => decide (x ∈ (D (k + j)).Dup)) : List _) :
          Multiset (A (k + j))) + ((l₀.filter (fun x => decide (x ∉ (D (k + j)).Dup)) :
            List _) : Multiset (A (k + j))) = Q₀.L := by
        rw [← hl₀]; exact AtomSolver.filter_split _ _
      apply SConstr.ext
      · simp [SConstr.wk]
      · simp only [SConstr.wk, add_L, map_L, Multiset.coe_nil, tsub_zero, Multiset.map_zero,
          zero_add]
        rw [hsplit]
    rw [e] at h
    have h' := WEntails.impl (D := D) Mult.omega h
    rw [omega_smul_of_unrestricted (Q := (⟨U, 0⟩ : SConstr (A k))) rfl] at h'
    refine .dom ?_ h'
    have hDup : (⟨∅, (Dl : Multiset (A k))⟩ : SConstr (A k)).InDup (D k).Dup :=
      fun x hx => hDl x hx
    rw [tsub_self, add_zero]
    have e2 : (⟨U, (Dl : Multiset (A k))⟩ : SConstr (A k)) = ⟨U, 0⟩ + ⟨∅, Dl⟩ := by
      ext x <;> simp
    rw [e2]
    exact hk.weaken_dup hDup (hk.refl _)
  | @empty k U Dl Li =>
    have hk := hD.lawful k
    refine ⟨le_refl _, (hD.wentails_simple_iff).mpr ?_⟩
    have hDup : (⟨∅, (Dl : Multiset (A k))⟩ : SConstr (A k)).InDup (D k).Dup :=
      fun x hx => hDl x hx
    rw [tsub_self, add_zero]
    have e2 : (⟨U, (Dl : Multiset (A k))⟩ : SConstr (A k)) = ⟨U, 0⟩ + ⟨∅, Dl⟩ := by
      ext x <;> simp
    rw [e2]
    exact hk.weaken_dup hDup (hk.unr_entails_zero (⟨U, 0⟩ : SConstr (A k)))
  | @split k U Dl Li Lo' Lo Q₁ Q₂ _ _ ih₁ ih₂ =>
    have hk := hD.lawful k
    obtain ⟨hle₁, h₁⟩ := ih₁ hDl
    obtain ⟨hle₂, h₂⟩ := ih₂ hDl
    refine ⟨hle₂.trans hle₁, ?_⟩
    have hDup : (⟨∅, (Dl : Multiset (A k))⟩ : SConstr (A k)).InDup (D k).Dup :=
      fun x hx => hDl x hx
    have e1 : ((Li : Multiset (A k)) - Lo) =
        ((Li : Multiset (A k)) - Lo') + ((Lo' : Multiset (A k)) - Lo) :=
      (tsub_add_tsub_cancel hle₁ hle₂).symm
    have e2 : (⟨U, (Dl : Multiset (A k)) + ((Li : Multiset (A k)) - Lo')⟩ : SConstr (A k)) +
        ⟨U, (Dl : Multiset (A k)) + ((Lo' : Multiset (A k)) - Lo)⟩ =
        (⟨∅, Dl⟩ + ⟨∅, Dl⟩) +
          ⟨U, ((Li : Multiset (A k)) - Lo') + ((Lo' : Multiset (A k)) - Lo)⟩ := by
      apply SConstr.ext
      · simp
      · simp only [add_L]; exact add_add_add_comm _ _ _ _
    have hT : D.WEntails ⟨U, (Dl : Multiset (A k)) + ((Li : Multiset (A k)) - Lo)⟩
        (.tensor (.simple Q₁) (.simple Q₂)) := by
      refine .dom ?_ (.tensor h₁ h₂)
      rw [e1, e2, AtomSolver.ctx_dup_split]
      exact hk.tensor (hk.dup_dup hDup) (hk.refl _)
    obtain ⟨X, E, Y, hE, hXEY, hX, hY⟩ := hD.inv_tensor hT
    rw [hXEY]
    exact (hD.wentails_simple_iff).mpr (hk.combine hE ((hD.wentails_simple_iff).mp hX)
      ((hD.wentails_simple_iff).mp hY))

-- [PAPER ◀ END] §6.3 › Lemma 6.5 (strengthened form)

-- [PAPER ▶ START] §6.3 › Lemma 6.5 "Constraint solver soundness", exactly as stated in the paper
/-- **Lemma 6.5 (Constraint solver soundness)**, in the paper's form: if
`U ; D ; Lᵢ ⊢s C ⇝ Lₒ` then `Lₒ ⊆ Lᵢ` and `(U, D ⊎ Lᵢ) ⊢ C ⊗ (∅, Lₒ)`. -/
theorem solve_sound {S : (k : Nat) → AtomSolver (A k)} (hS : ∀ k, (S k).Sound (D k))
    {k : Nat} {U : Finset (A k)} {Dl Li Lo : List (A k)} {C : Wanted A k}
    (h : Solve D S U Dl Li C Lo) (hDl : ∀ x ∈ Dl, x ∈ (D k).Dup) :
    (Lo : Multiset (A k)) ≤ Li ∧
      D.WEntails ⟨U, (Dl : Multiset (A k)) + Li⟩ (.tensor C (.simple ⟨∅, Lo⟩)) := by
  obtain ⟨hle, h'⟩ := hD.solve_sound_strong hS h hDl
  refine ⟨hle, ?_⟩
  rw [AtomSolver.ctx_split U Dl Li Lo hle]
  exact .tensor h' (.id _)

-- [PAPER ◀ END] §6.3 › Lemma 6.5 (paper form)

end LDomain.Lawful

-- [NOT IN PAPER ▶ START] end-to-end soundness of inference: not stated in the paper; it combines
--   Lemma 6.4 (§6.2) and Lemma 6.5 (§6.3), as the opening paragraph of §6.3 suggests
/-- **End-to-end soundness of constraint inference** (Lemma 6.4 combined with Lemma 6.5): if
`Γ ⊢ᵢ e : τ ⇝ C` and `U ; D ; L ⊢s C ⇝ ∅` then `(U, D ⊎ L) ; Γ ⊢ e : τ`. -/
theorem LDomain.Lawful.infer_sound {P : Type} {D : LDomain (Atom P)} (hD : D.Lawful)
    {S : (k : Nat) → AtomSolver (Atom P k)} (hS : ∀ k, (S k).Sound (D k)) {sig : DataSig P}
    {k n : Nat} {Γ : Fin n → Scheme P k} {u : Fin n → Usage} {e : Tm sig k n} {τ : Ty P k}
    {C : Wanted (Atom P) k} (hG : Gen sig Γ u e τ C) {U : Finset (Atom P k)}
    {Dl L : List (Atom P k)} (hDl : ∀ x ∈ Dl, x ∈ (D k).Dup) (h : Solve D S U Dl L C []) :
    Nonempty (HasType D sig ⟨U, (Dl : Multiset (Atom P k)) + L⟩ Γ u e τ) := by
  obtain ⟨-, h'⟩ := hD.solve_sound_strong hS h hDl
  rw [Multiset.coe_nil, tsub_zero] at h'
  exact hD.gen_sound hG h'

-- [NOT IN PAPER ◀ END] end-to-end soundness

end Leveled

end LQT
