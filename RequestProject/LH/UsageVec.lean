module

public import RequestProject.LH.Typing

/-!
# Usage vectors (infrastructure for the metatheory of `λq→`)

No counterpart in the paper.  `mix w u = Σₓ u x • w x` is the usage vector obtained by
replacing each variable `x` (used `u x` times) by a term whose usage vector is `w x`; it is the
usage vector of a renamed or substituted term.
-/

@[expose] public section

namespace LH

-- [NOT IN PAPER ▶ START] usage vectors
variable {m n n' : Nat}

/-- `mix w u = Σₓ u x • w x`. -/
def mix (w : Fin n → Fin n' → Usage m) (u : Fin n → Usage m) : Fin n' → Usage m :=
  ∑ x, u x • w x

theorem mix_add (w : Fin n → Fin n' → Usage m) (u₁ u₂ : Fin n → Usage m) :
    mix w (u₁ + u₂) = mix w u₁ + mix w u₂ := by
  simp [mix, add_smul, Finset.sum_add_distrib]

theorem mix_smul (w : Fin n → Fin n' → Usage m) (c : Usage m) (u : Fin n → Usage m) :
    mix w (c • u) = c • mix w u := by
  simp [mix, Finset.smul_sum, mul_smul]

theorem mix_single (w : Fin n → Fin n' → Usage m) (x : Fin n) :
    mix w (Pi.single x 1) = w x := by
  unfold mix
  rw [Finset.sum_eq_single x]
  · simp
  · intro y _ hy; simp [hy]
  · simp

theorem mix_sum {ι : Type} [Fintype ι] (w : Fin n → Fin n' → Usage m)
    (f : ι → Fin n → Usage m) : mix w (∑ i, f i) = ∑ i, mix w (f i) := by
  unfold mix
  simp only [Finset.sum_apply, Finset.sum_smul]
  exact Finset.sum_comm

theorem mix_omega_single_sum (w : Fin n → Fin n' → Usage m) (v : Fin n → Usage m)
    (x : Fin n) :
    mix w ((Usage.omega : Usage m) • v + Pi.single x 1) =
      (Usage.omega : Usage m) • mix w v + w x := by
  rw [mix_add, mix_smul, mix_single]

/-- The weakening of a usage vector by a new multiplicity variable. -/
def wkU (u : Fin n → Usage m) : Fin n → Usage (m + 1) := fun x => Usage.wk (u x)

theorem wkU_add (u v : Fin n → Usage m) : wkU (u + v) = wkU u + wkU v := by
  funext x; simp [wkU]

theorem wkU_smul (c : Usage m) (u : Fin n → Usage m) : wkU (c • u) = Usage.wk c • wkU u := by
  funext x; simp [wkU]

theorem wkU_sum {ι : Type} [Fintype ι] (f : ι → Fin n → Usage m) :
    wkU (∑ i, f i) = ∑ i, wkU (f i) := by
  funext x; simp [wkU, Finset.sum_apply, map_sum]

theorem wkU_single (x : Fin n) : wkU (Pi.single x (1 : Usage m)) = Pi.single x 1 := by
  funext y; by_cases h : y = x
  · subst h; simp [wkU]
  · simp [wkU, h]

theorem wkU_mix (w : Fin n → Fin n' → Usage m) (u : Fin n → Usage m) :
    wkU (mix w u) = mix (fun x => wkU (w x)) (wkU u) := by
  simp only [mix, wkU_sum, wkU_smul]
  rfl

@[simp] theorem Usage.wk_omega : Usage.wk (Usage.omega : Usage m) = Usage.omega := rfl
@[simp] theorem Usage.wk_nz (a : Mult m) : Usage.wk (Usage.nz a) = Usage.nz a.wk := rfl

theorem Usage.subst_wkU {m' : Nat} (s : Fin m → Mult m') (u : Fin n → Usage m) :
    (fun x => Usage.subst (Mult.liftS s) (wkU u x)) = wkU (fun x => Usage.subst s (u x)) := by
  funext x; exact Usage.subst_liftS_wk s (u x)

/-! ### Extension of contexts by one variable -/

theorem cons_add_cons (a b : Usage m) (u v : Fin n → Usage m) :
    (Fin.cons a u : Fin (n + 1) → Usage m) + Fin.cons b v = Fin.cons (a + b) (u + v) := by
  funext y; refine Fin.cases ?_ (fun z => ?_) y <;> simp

theorem smul_cons (c a : Usage m) (u : Fin n → Usage m) :
    c • (Fin.cons a u : Fin (n + 1) → Usage m) = Fin.cons (c * a) (c • u) := by
  funext y; refine Fin.cases ?_ (fun z => ?_) y <;> simp

theorem single_zero_eq_cons : (Pi.single 0 (1 : Usage m) : Fin (n + 1) → Usage m) =
    Fin.cons 1 0 := by
  funext y; refine Fin.cases ?_ (fun z => ?_) y
  · simp
  · simp [Fin.succ_ne_zero]

theorem single_succ_eq_cons (x : Fin n) :
    (Pi.single x.succ (1 : Usage m) : Fin (n + 1) → Usage m) = Fin.cons 0 (Pi.single x 1) := by
  funext y; refine Fin.cases ?_ (fun z => ?_) y
  · simp [(Fin.succ_ne_zero x).symm]
  · simp [Pi.single_apply, Fin.succ_inj]

theorem mix_cons (w : Fin n → Fin n' → Usage m) (a : Usage m) (u : Fin n → Usage m) :
    mix (Fin.cons (Pi.single 0 1) (fun x => Fin.cons 0 (w x))) (Fin.cons a u) =
      Fin.cons a (mix w u) := by
  unfold mix
  rw [Fin.sum_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ]
  funext y; refine Fin.cases ?_ (fun z => ?_) y
  · simp [Finset.sum_apply]
  · simp [Finset.sum_apply, Fin.succ_ne_zero]

theorem mix_single_succ (v : Fin n → Usage m) :
    mix (fun y => Pi.single y.succ 1) v = (Fin.cons 0 v : Fin (n + 1) → Usage m) := by
  funext y; refine Fin.cases ?_ (fun z => ?_) y
  · simp [mix, Finset.sum_apply, (Fin.succ_ne_zero _).symm]
  · simp only [mix, Finset.sum_apply, Pi.smul_apply, Fin.cons_succ]
    rw [Finset.sum_eq_single z]
    · simp
    · intro b _ hb; simp [Fin.succ_inj, Ne.symm hb]
    · simp

/-! ### Extension of contexts by a block of variables -/

theorem append_add_append {j : Nat} (u v : Fin n → Usage m) (f g : Fin j → Usage m) :
    Fin.append u f + Fin.append v g = Fin.append (u + v) (f + g) := by
  funext y; refine Fin.addCases (fun z => ?_) (fun z => ?_) y <;> simp

theorem smul_append {j : Nat} (c : Usage m) (u : Fin n → Usage m) (f : Fin j → Usage m) :
    c • Fin.append u f = Fin.append (c • u) (c • f) := by
  funext y; refine Fin.addCases (fun z => ?_) (fun z => ?_) y <;> simp

theorem append_zero_zero {j : Nat} :
    Fin.append (0 : Fin n → Usage m) (0 : Fin j → Usage m) = 0 := by
  funext y; refine Fin.addCases (fun z => ?_) (fun z => ?_) y <;> simp

theorem single_castAdd {j : Nat} (x : Fin n) :
    (Pi.single (Fin.castAdd j x) (1 : Usage m) : Fin (n + j) → Usage m) =
      Fin.append (Pi.single x 1) 0 := by
  funext y; refine Fin.addCases (fun z => ?_) (fun z => ?_) y
  · by_cases h : z = x
    · subst h; simp
    · simp [h, Fin.castAdd_inj]
  · simp only [Fin.append_right, Pi.zero_apply]
    rw [Pi.single_apply, if_neg]
    intro h
    exact absurd (congrArg Fin.val h) (by simp; omega)

theorem single_natAdd {j : Nat} (i : Fin j) :
    (Pi.single (Fin.natAdd n i) (1 : Usage m) : Fin (n + j) → Usage m) =
      Fin.append 0 (Pi.single i 1) := by
  funext y; refine Fin.addCases (fun z => ?_) (fun z => ?_) y
  · simp only [Fin.append_left, Pi.zero_apply]
    rw [Pi.single_apply, if_neg]
    intro h
    exact absurd (congrArg Fin.val h) (by simp; omega)
  · by_cases h : z = i
    · subst h; simp
    · simp [h, Fin.natAdd_inj]

theorem mix_append {j : Nat} (w : Fin n → Fin n' → Usage m) (u : Fin n → Usage m)
    (f : Fin j → Usage m) :
    mix (Fin.append (fun x => Fin.append (w x) 0) (fun i => Pi.single (Fin.natAdd n' i) 1))
        (Fin.append u f) = Fin.append (mix w u) f := by
  unfold mix
  rw [Fin.sum_univ_add]
  simp only [Fin.append_left, Fin.append_right, single_natAdd]
  funext y; refine Fin.addCases (fun z => ?_) (fun z => ?_) y
  · simp [Finset.sum_apply]
  · simp only [Finset.sum_apply, Pi.add_apply, Pi.smul_apply, Fin.append_right, Pi.zero_apply,
      smul_zero, Finset.sum_const_zero, zero_add]
    rw [Finset.sum_eq_single z]
    · simp
    · intro b _ hb; simp [Ne.symm hb]
    · simp

theorem mix_single_castAdd {j : Nat} (v : Fin n → Usage m) :
    mix (fun y => Pi.single (Fin.castAdd j y) 1) v =
      (Fin.append v 0 : Fin (n + j) → Usage m) := by
  simp only [single_castAdd]
  unfold mix
  funext y; refine Fin.addCases (fun z => ?_) (fun z => ?_) y
  · simp only [Finset.sum_apply, Pi.smul_apply, Fin.append_left]
    rw [Finset.sum_eq_single z]
    · simp
    · intro b _ hb; simp [Ne.symm hb]
    · simp
  · simp [Finset.sum_apply]

theorem mix_single_self (u : Fin n → Usage m) : mix (fun x => Pi.single x 1) u = u := by
  funext y
  simp only [mix, Finset.sum_apply, Pi.smul_apply]
  rw [Finset.sum_eq_single y]
  · simp
  · intro b _ hb; simp [Ne.symm hb]
  · simp
-- [NOT IN PAPER ◀ END]

end LH
