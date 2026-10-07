module

public import RequestProject.LQT.Ch6_ConstraintInference.Solver

/-!
# The atomic-constraint solver of Figure 10b (§6.3.2)

Paper location: §6.3.2 "An atomic-constraint solver", Figure 10 "A stripped-down constraint
domain", sub-figure (b) "Atomic-constraint solver".  The start and end of each part is marked by
`-- [PAPER ▶ START]` / `-- [PAPER ◀ END]` comments.

* `simpleSolver l` : the rules of Figure 10b, for the domain in which the distinguished
  constraint `𝓛` (`l`, modelling `Linearly`) is duplicable;
* `simpleSolver_sound` : it satisfies the (strengthened) atomic-solver soundness property
  `AtomSolver.Sound` required by Lemma 6.5 (not proved in the paper).

Note on Figure 10b: rule `Atom_OneD` is printed with conclusion `U ; D, 𝓛 ; L ⊢ 1·q ⇝ L` for an
arbitrary `q`; read literally this would solve every linear constraint as soon as a `Linearly`
assumption is available, which is unsound.  We read it with `q = 𝓛`.
-/

@[expose] public section

namespace LQT

open SConstr

section

variable {A : Type*} [DecidableEq A]

-- [PAPER ▶ START] §6.3.2 › Figure 10 "A stripped-down constraint domain", (b) "Atomic-constraint
--   solver" (one constructor per rule)
/-- The atomic-constraint solver of Figure 10b, for the stripped-down domain in which the
distinguished constraint `𝓛` (`l`, modelling `Linearly`) is duplicable. -/
inductive simpleSolver (l : A) : AtomSolver A
  /-- Atom_Many -/
  | many {U Dl Li q} : q ∈ U → simpleSolver l U Dl Li .omega q Li
  /-- Atom_OneL: use the most recent linear occurrence of `q`. -/
  | oneL {U Dl q} (L₁ L₂ : List A) : q ∉ L₂ → q ∉ U →
      simpleSolver l U Dl (L₁ ++ q :: L₂) .one q (L₁ ++ L₂)
  /-- Atom_OneD -/
  | oneD {U Dl Li} : l ∉ U → simpleSolver l U (Dl ++ [l]) Li .one l Li
  /-- Atom_OneU -/
  | oneU {U Dl Li q} : q ∈ U → q ∉ Dl ++ Li → simpleSolver l U Dl Li .one q Li

-- [PAPER ◀ END] §6.3.2 › Figure 10b

-- [NOT IN PAPER ▶ START] soundness of the solver of Figure 10b: the paper does not prove that it
--   satisfies Property 6.6
/-- The atomic-constraint solver of Figure 10b is sound (in the strengthened sense, hence also
in the sense of Property 6.6) for every lawful domain — in particular for the stripped-down
domain `freeDomain {𝓛}`.  (Rule Atom_OneD only fires when `𝓛` is in the duplicable context
`D`, whose elements are duplicable by the solver's invariant.) -/
theorem simpleSolver_sound {D : Domain A} (hD : D.Lawful) (l : A) :
    (simpleSolver l).Sound D := by
  intro U Dl Li π q Lo hDl h
  have hDup : (⟨∅, (Dl : Multiset A)⟩ : SConstr A).InDup D.Dup := fun x hx => hDl x hx
  cases h with
  | many hq =>
    refine ⟨le_refl _, ?_⟩
    rw [tsub_self, add_zero]
    have e : (⟨U, (Dl : Multiset A)⟩ : SConstr A) = (⟨U, 0⟩ : SConstr A).unr + ⟨∅, Dl⟩ := by
      ext x <;> simp
    rw [e]
    exact hD.weaken_dup hDup (hD.unr_entails_of_subset rfl (by simpa using hq))
  | oneL L₁ L₂ hq₂ hqU =>
    have hperm : ((L₁ ++ q :: L₂ : List A) : Multiset A) = ((L₁ ++ L₂ : List A) : Multiset A) + {q} := by
      rw [Multiset.coe_eq_coe.mpr List.perm_middle, ← Multiset.cons_coe,
        ← Multiset.singleton_add, add_comm]
    refine ⟨by rw [hperm]; exact le_add_right (le_refl _), ?_⟩
    rw [hperm, add_tsub_cancel_left]
    have e : (⟨U, (Dl : Multiset A) + {q}⟩ : SConstr A) = ⟨U, 0⟩ + (atom .one q + ⟨∅, Dl⟩) := by
      ext x <;> simp [add_comm]
    rw [e]
    exact hD.weaken_unr rfl (hD.weaken_dup hDup (hD.refl _))
  | @oneD U Dl' Li hlU =>
    refine ⟨le_refl _, ?_⟩
    rw [tsub_self, add_zero]
    have hDup' : (⟨∅, (Dl' : Multiset A)⟩ : SConstr A).InDup D.Dup :=
      fun x hx => hDl x (List.mem_append_left _ hx)
    have e : (⟨U, ((Dl' ++ [l] : List A) : Multiset A)⟩ : SConstr A) =
        ⟨U, 0⟩ + (atom .one l + ⟨∅, Dl'⟩) := by
      ext x
      · simp
      · simp [← Multiset.coe_add, add_comm]
    rw [e]
    exact hD.weaken_unr rfl (hD.weaken_dup hDup' (hD.refl _))
  | oneU hqU _ =>
    refine ⟨le_refl _, ?_⟩
    rw [tsub_self, add_zero]
    have e : (⟨U, (Dl : Multiset A)⟩ : SConstr A) = (⟨U, 0⟩ : SConstr A).unr + ⟨∅, Dl⟩ := by
      ext x <;> simp
    rw [e]
    refine hD.weaken_dup hDup (hD.trans (hD.unr_entails_of_subset (X := atom .omega q) rfl
      (by simpa using hqU)) ?_)
    have := hD.omega_smul_entails (atom .one q)
    rwa [smul_atom] at this

-- [NOT IN PAPER ◀ END] soundness of the solver of Figure 10b

end

end LQT
