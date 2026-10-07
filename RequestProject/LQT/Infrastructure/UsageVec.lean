module

public import RequestProject.LQT.Infrastructure.Usage

/-!
# Usage vectors and renamings

Technical lemmas on usage vectors (`Fin n → Usage`) used by the desugaring proof: transport of
a usage vector along an injective renaming (`push`), and the interaction of context extension
(`Fin.cons`, `Fin.append`) with addition and scaling.

Paper location: none.  This whole file is formalization infrastructure (the paper uses named
contexts and needs no renaming lemmas).
-/

@[expose] public section

namespace LQT

-- [NOT IN PAPER ▶ START] usage-vector algebra for renamings (whole file)

open Function

/-- Transport of a usage vector along a renaming `ρ`; variables outside the image of `ρ` get
usage `0`. -/
noncomputable def push {n m : Nat} (ρ : Fin n → Fin m) (u : Fin n → Usage) : Fin m → Usage :=
  Function.extend ρ u 0

/-- Renaming into a context extended by one variable at index `0`. -/
def shift {n m : Nat} (ρ : Fin n → Fin m) : Fin n → Fin (m + 1) := fun i => (ρ i).succ

/-- Lifting a renaming under one binder. -/
def liftR {n m : Nat} (ρ : Fin n → Fin m) : Fin (n + 1) → Fin (m + 1) :=
  Fin.cases 0 (fun i => (ρ i).succ)

/-- Lifting a renaming under `k` binders. -/
def liftRN (k : Nat) {n m : Nat} (ρ : Fin n → Fin m) : Fin (k + n) → Fin (k + m) :=
  Fin.addCases (fun j => Fin.castAdd m j) (fun i => Fin.natAdd k (ρ i))

section
variable {n m : Nat}

@[simp] lemma shift_apply (ρ : Fin n → Fin m) (i : Fin n) : shift ρ i = (ρ i).succ := rfl
@[simp] lemma liftR_zero (ρ : Fin n → Fin m) : liftR ρ 0 = 0 := rfl
@[simp] lemma liftR_succ (ρ : Fin n → Fin m) (i : Fin n) : liftR ρ i.succ = (ρ i).succ := rfl
@[simp] lemma liftRN_castAdd (k : Nat) (ρ : Fin n → Fin m) (j : Fin k) :
    liftRN k ρ (Fin.castAdd n j) = Fin.castAdd m j := by
  simp [liftRN]
@[simp] lemma liftRN_natAdd (k : Nat) (ρ : Fin n → Fin m) (i : Fin n) :
    liftRN k ρ (Fin.natAdd k i) = Fin.natAdd k (ρ i) := by
  simp [liftRN]

lemma shift_injective {ρ : Fin n → Fin m} (hρ : Injective ρ) : Injective (shift ρ) :=
  fun _ _ h => hρ (Fin.succ_injective _ h)

lemma liftR_injective {ρ : Fin n → Fin m} (hρ : Injective ρ) : Injective (liftR ρ) := by
  intro i j h
  cases i using Fin.cases with
  | zero =>
    cases j using Fin.cases with
    | zero => rfl
    | succ j' => simp only [liftR_zero, liftR_succ] at h; exact absurd h.symm (Fin.succ_ne_zero _)
  | succ i' =>
    cases j using Fin.cases with
    | zero => simp only [liftR_zero, liftR_succ] at h; exact absurd h (Fin.succ_ne_zero _)
    | succ j' =>
      simp only [liftR_succ] at h
      exact congrArg Fin.succ (hρ (Fin.succ_injective _ h))

lemma liftRN_injective (k : Nat) {ρ : Fin n → Fin m} (hρ : Injective ρ) :
    Injective (liftRN k ρ) := by
  intro i j
  refine Fin.addCases (fun i' => ?_) (fun i' => ?_) i <;>
    refine Fin.addCases (fun j' => ?_) (fun j' => ?_) j <;> intro h <;> simp at h
  · rw [h]
  · exact absurd (congrArg Fin.val h) (by simp; omega)
  · exact absurd (congrArg Fin.val h) (by simp; omega)
  · rw [hρ h]

lemma push_apply {ρ : Fin n → Fin m} (hρ : Injective ρ) (u : Fin n → Usage) (i : Fin n) :
    push ρ u (ρ i) = u i :=
  hρ.extend_apply u 0 i

lemma push_apply_of_not {ρ : Fin n → Fin m} {u : Fin n → Usage} {j : Fin m}
    (h : ∀ i, ρ i ≠ j) : push ρ u j = 0 :=
  Function.extend_apply' _ _ _ (by rintro ⟨i, hi⟩; exact h i hi)

lemma push_eq {ρ : Fin n → Fin m} (hρ : Injective ρ) {u : Fin n → Usage} {v : Fin m → Usage}
    (h₁ : ∀ i, v (ρ i) = u i) (h₂ : ∀ j, (∀ i, ρ i ≠ j) → v j = 0) : push ρ u = v := by
  funext j
  by_cases h : ∃ i, ρ i = j
  · obtain ⟨i, rfl⟩ := h
    rw [push_apply hρ, h₁]
  · push_neg at h
    rw [push_apply_of_not h, h₂ j h]

lemma push_add {ρ : Fin n → Fin m} (hρ : Injective ρ) (u v : Fin n → Usage) :
    push ρ (u + v) = push ρ u + push ρ v :=
  push_eq hρ (by simp [push_apply hρ]) (by intro j h; simp [push_apply_of_not h])

lemma push_smul {ρ : Fin n → Fin m} (hρ : Injective ρ) (π : Mult) (u : Fin n → Usage) :
    push ρ (π • u) = π • push ρ u :=
  push_eq hρ (by simp [push_apply hρ]) (by intro j h; simp [push_apply_of_not h])

lemma push_zero {ρ : Fin n → Fin m} (hρ : Injective ρ) : push ρ (0 : Fin n → Usage) = 0 :=
  push_eq hρ (by simp) (by simp)

lemma push_single {ρ : Fin n → Fin m} (hρ : Injective ρ) (x : Fin n) :
    push ρ (single x) = single (ρ x) := by
  refine push_eq hρ (fun i => ?_) (fun j h => ?_)
  · simp [single, hρ.eq_iff]
  · have : j ≠ ρ x := fun e => h x e.symm
    simp [single, this]

lemma push_shift {ρ : Fin n → Fin m} (hρ : Injective ρ) (u : Fin n → Usage) :
    push (shift ρ) u = Fin.cons 0 (push ρ u) := by
  refine push_eq (shift_injective hρ) (fun i => ?_) (fun j h => ?_)
  · simp [push_apply hρ]
  · cases j using Fin.cases with
    | zero => rfl
    | succ j' =>
      simp only [Fin.cons_succ]
      exact push_apply_of_not (fun i e => h i (by simp [e]))

lemma push_liftR {ρ : Fin n → Fin m} (hρ : Injective ρ) (a : Usage) (u : Fin n → Usage) :
    push (liftR ρ) (Fin.cons a u) = Fin.cons a (push ρ u) := by
  refine push_eq (liftR_injective hρ) (fun i => ?_) (fun j h => ?_)
  · refine Fin.cases ?_ (fun i' => ?_) i
    · rfl
    · simp [push_apply hρ]
  · cases j using Fin.cases with
    | zero => exact absurd (liftR_zero ρ) (h 0)
    | succ j' =>
      simp only [Fin.cons_succ]
      exact push_apply_of_not (fun i e => h i.succ (by simp [e]))

lemma push_liftRN (k : Nat) {ρ : Fin n → Fin m} (hρ : Injective ρ) (f : Fin k → Usage)
    (u : Fin n → Usage) :
    push (liftRN k ρ) (Fin.append f u) = Fin.append f (push ρ u) := by
  refine push_eq (liftRN_injective k hρ) (fun i => ?_) (fun j h => ?_)
  · refine Fin.addCases (fun i' => ?_) (fun i' => ?_) i
    · simp
    · simp [push_apply hρ]
  · revert h
    refine Fin.addCases (fun j' => ?_) (fun j' => ?_) j <;> intro h
    · exact absurd (liftRN_castAdd k ρ j') (h _)
    · simp only [Fin.append_right]
      exact push_apply_of_not (fun i e => h (Fin.natAdd k i) (by simp [e]))

/-! ### Context extension and arithmetic -/

lemma cons_add_cons (a b : Usage) (u v : Fin n → Usage) :
    (Fin.cons a u : Fin (n + 1) → Usage) + Fin.cons b v = Fin.cons (a + b) (u + v) := by
  funext i; refine Fin.cases ?_ (fun i' => ?_) i <;> simp

lemma smul_cons (π : Mult) (a : Usage) (u : Fin n → Usage) :
    π • (Fin.cons a u : Fin (n + 1) → Usage) = Fin.cons (π • a) (π • u) := by
  funext i; refine Fin.cases ?_ (fun i' => ?_) i <;> simp

lemma single_zero_eq : (single 0 : Fin (n + 1) → Usage) = Fin.cons Usage.one 0 := by
  funext i; refine Fin.cases ?_ (fun i' => ?_) i <;> simp [single, Fin.succ_ne_zero]

lemma single_succ_eq (j : Fin n) : (single j.succ : Fin (n + 1) → Usage) = Fin.cons 0 (single j) := by
  funext i; refine Fin.cases ?_ (fun i' => ?_) i
  · simp [single, (Fin.succ_ne_zero j).symm]
  · simp [single]

lemma zero_eq_cons : (0 : Fin (n + 1) → Usage) = Fin.cons 0 0 := by
  funext i; refine Fin.cases ?_ (fun i' => ?_) i <;> simp

lemma append_add_append {k : Nat} (f g : Fin k → Usage) (u v : Fin n → Usage) :
    Fin.append f u + Fin.append g v = Fin.append (f + g) (u + v) := by
  funext i; refine Fin.addCases (fun i' => ?_) (fun i' => ?_) i <;> simp

lemma smul_append {k : Nat} (π : Mult) (f : Fin k → Usage) (u : Fin n → Usage) :
    π • Fin.append f u = Fin.append (π • f) (π • u) := by
  funext i; refine Fin.addCases (fun i' => ?_) (fun i' => ?_) i <;> simp

lemma single_natAdd {k : Nat} (j : Fin n) :
    (single (Fin.natAdd k j) : Fin (k + n) → Usage) = Fin.append 0 (single j) := by
  funext i; refine Fin.addCases (fun i' => ?_) (fun i' => ?_) i
  · have : Fin.castAdd n i' ≠ Fin.natAdd k j := by
      intro h; have := congrArg Fin.val h; simp at this; omega
    simp [single, this]
  · simp [single]

end

-- [NOT IN PAPER ◀ END] usage-vector algebra

end LQT
