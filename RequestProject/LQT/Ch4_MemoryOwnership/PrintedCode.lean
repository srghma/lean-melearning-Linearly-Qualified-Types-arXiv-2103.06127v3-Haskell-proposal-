module

public import RequestProject.LQT.Ch4_MemoryOwnership.Setting

/-!
# The code of §4 and §6.3.2 as printed is ill typed

Paper location: §3 Figure 1b (type of `new`), §6.3.2 (the example `f`, which writes
`pack (Ur arr) = new 10`) and §4.2 Figure 3 (`sort`, which writes
`pack pivotIdx = partition arr` and then `split arr pivotIdx`).

A variable bound by `let pack x = e₁ in e₂` is linear (rules E_Unpack and G_Unpack bind it with
multiplicity `1`).  Passing it to an unrestricted argument (an arrow `->`) uses it `ω` times, so
no typing derivation exists, whatever the given constraints, the type and the usages.  This
justifies items 1 and 2 of `CORRECTIONS.md`:

* `unpack_then_unrestricted_rejected`: the general fact, for any expression `e₁` that is
  unpacked and any function `f` whose argument is unrestricted.
* `unpack_free_rejected`: with the type `new :: Linearly =⚬ Int -> ∃ n. UArray a n ⧀ RW n` of
  Figure 1b, the only way to get at the array is `let pack arr = new 10 in …`, and then
  `free arr` is ill typed (`free :: RW n =⚬ UArray a n -> ()`).
* `sort_printed_rejected`: Figure 3's
  `let pack pivotIdx = partition arr; pack (Ur (l, r)) = split arr pivotIdx; … ` is ill typed
  for *every* continuation `…` and every definition of `partition arr`, because
  `split :: RW n =⚬ PArray a n -> Int -> …` takes the index unrestrictedly.

Since inference is sound (`Infers.typed`), these programs are rejected by the inference
algorithm too.  The corrected versions (`new` returning `Ur (UArray a n)`, `partition`
returning `Ur Int` unpacked as `pack (Ur pivotIdx)`) are accepted: `fLinearly_inferred`,
`sort_inferred`.
-/

@[expose] public section

namespace LQT

-- [NOT IN PAPER ▶ START] usage-tracking inversion lemmas

lemma one_add_omega_smul_ne_zero (a : Usage) : Usage.one + (Mult.omega : Mult) • a ≠ 0 := by
  cases a <;> decide

namespace HasType

variable {P : Type} {D : LDomain (Atom P)} {sig : DataSig P}

/-- Inversion for variables, keeping the usage: `x` is used at least once. -/
theorem var_invU {k n : Nat} {Q : SConstr (Atom P k)} {Γ : Fin n → Scheme P k}
    {u : Fin n → Usage} {x : Fin n} {τ : Ty P k} (d : HasType D sig Q Γ u (.var x) τ) :
    u x ≠ 0 ∧ ∃ τs : Fin (Γ x).j → Ty P k, τ = (Γ x).τ.subst (instSub τs) := by
  generalize he : (Tm.var x : Tm sig k n) = e at d
  induction d with
  | var v τs hx =>
    cases he; subst hx
    refine ⟨?_, τs, rfl⟩
    simp only [Pi.add_apply, Pi.smul_apply, single, if_true]
    exact one_add_omega_smul_ne_zero _
  | sub _ _ ih => exact ih he
  | _ => cases he

/-- Inversion for applications, keeping the usages. -/
theorem app_invU {k n : Nat} {Q : SConstr (Atom P k)} {Γ : Fin n → Scheme P k}
    {u : Fin n → Usage} {e₁ e₂ : Tm sig k n} {τ : Ty P k}
    (d : HasType D sig Q Γ u (.app e₁ e₂) τ) :
    ∃ (Q₁ Q₂ : SConstr (Atom P k)) (u₁ u₂ : Fin n → Usage) (π : Mult) (τ₁ : Ty P k),
      u = u₁ + π • u₂ ∧ Nonempty (HasType D sig Q₁ Γ u₁ e₁ (.arr π τ₁ τ)) ∧
      Nonempty (HasType D sig Q₂ Γ u₂ e₂ τ₁) := by
  generalize he : (Tm.app e₁ e₂ : Tm sig k n) = e at d
  induction d with
  | app d₁ d₂ _ _ =>
    cases he
    exact ⟨_, _, _, _, _, _, rfl, ⟨d₁⟩, ⟨d₂⟩⟩
  | sub _ _ ih => exact ih he
  | _ => cases he

/-- Inversion for unpacking, keeping the usages: the bound variable has usage `1` in the body. -/
theorem unpack_invU {k n j : Nat} {Q : SConstr (Atom P k)} {Γ : Fin n → Scheme P k}
    {u : Fin n → Usage} {e₁ : Tm sig k n} {e₂ : Tm sig (k + j) (n + 1)} {τ : Ty P k}
    (d : HasType D sig Q Γ u (.unpack j e₁ e₂) τ) :
    ∃ (Q₂ : SConstr (Atom P (k + j))) (u₂ : Fin n → Usage) (τ₁ : Ty P (k + j)),
      Nonempty (HasType D sig Q₂ (Fin.cons (Scheme.mono τ₁) (ctxWk j Γ))
        (Fin.cons Usage.one u₂) e₂ (τ.wk j)) := by
  generalize he : (Tm.unpack j e₁ e₂ : Tm sig k n) = e at d
  induction d with
  | unpack _ d₂ _ _ =>
    cases he
    exact ⟨_, _, _, ⟨d₂⟩⟩
  | sub _ _ ih => exact ih he
  | _ => cases he

/-- Inversion for unpacking, keeping the usages of the unpacked expression. -/
theorem unpack_invU₁ {k n j : Nat} {Q : SConstr (Atom P k)} {Γ : Fin n → Scheme P k}
    {u : Fin n → Usage} {e₁ : Tm sig k n} {e₂ : Tm sig (k + j) (n + 1)} {τ : Ty P k}
    (d : HasType D sig Q Γ u (.unpack j e₁ e₂) τ) :
    ∃ (Q₁ : SConstr (Atom P k)) (u₁ u₂ : Fin n → Usage) (τ₁ : Ty P k),
      u = u₁ + u₂ ∧ Nonempty (HasType D sig Q₁ Γ u₁ e₁ τ₁) := by
  generalize he : (Tm.unpack j e₁ e₂ : Tm sig k n) = e at d
  induction d with
  | unpack d₁ _ _ _ =>
    cases he
    exact ⟨_, _, _, _, rfl, ⟨d₁⟩⟩
  | sub _ _ ih => exact ih he
  | _ => cases he

/-- If every typing of `f` is an unrestricted arrow, then `f x` uses `x` `ω` times. -/
theorem app_var_omega {k n : Nat} {Q : SConstr (Atom P k)} {Γ : Fin n → Scheme P k}
    {u : Fin n → Usage} {f : Tm sig k n} {x : Fin n} {τ : Ty P k}
    (hf : ∀ (Q' : SConstr (Atom P k)) (u' : Fin n → Usage) (π : Mult) (τ₁ τ₂ : Ty P k),
      HasType D sig Q' Γ u' f (.arr π τ₁ τ₂) → π = .omega)
    (d : HasType D sig Q Γ u (.app f (.var x)) τ) : u x = .omega := by
  obtain ⟨Q₁, Q₂, u₁, u₂, π, τ₁, rfl, ⟨d₁⟩, ⟨d₂⟩⟩ := app_invU d
  obtain rfl := hf _ _ _ _ _ d₁
  have h := (var_invU d₂).1
  simp only [Pi.add_apply, Pi.smul_apply]
  generalize u₂ x = a at h
  cases a
  · exact absurd rfl h
  · simp
  · simp

lemma arr_subst_omega {k : Nat} (σ : Scheme P k) (τs : Fin σ.j → Ty P k)
    {π : Mult} {τ₁ τ₂ : Ty P k} (hσ : ∃ a b, σ.τ = .arr .omega a b)
    (h : Ty.arr π τ₁ τ₂ = σ.τ.subst (instSub τs)) : π = .omega := by
  obtain ⟨a, b, hab⟩ := hσ
  rw [hab] at h
  simp only [Ty.subst] at h
  exact (Ty.arr.inj h).1

lemma arr_arr_subst_omega {k : Nat} (σ : Scheme P k) (τs : Fin σ.j → Ty P k)
    {π π' : Mult} {τ' τ₁ τ₂ : Ty P k} (hσ : ∃ π₀ a b c, σ.τ = .arr π₀ a (.arr .omega b c))
    (h : Ty.arr π' τ' (Ty.arr π τ₁ τ₂) = σ.τ.subst (instSub τs)) : π = .omega := by
  obtain ⟨π₀, a, b, c, hab⟩ := hσ
  rw [hab] at h
  simp only [Ty.subst] at h
  exact (Ty.arr.inj (Ty.arr.inj h).2.2).1

/-- A variable's argument is unrestricted when its type scheme is `∀ā. Q ⇒ τ₁ → τ₂`, whatever
the instantiation. -/
theorem var_arr_omega {k n : Nat} {Γ : Fin n → Scheme P k} {x : Fin n}
    (hx : ∃ τ₁ τ₂, (Γ x).τ = .arr .omega τ₁ τ₂) (Q' : SConstr (Atom P k)) (u' : Fin n → Usage)
    (π : Mult) (τ₁ τ₂ : Ty P k) (d : HasType D sig Q' Γ u' (.var x) (.arr π τ₁ τ₂)) :
    π = .omega := by
  obtain ⟨-, τs, h⟩ := var_invU d
  exact arr_subst_omega (Γ x) τs hx h

/-- A partial application `g y` has an unrestricted argument when `g`'s scheme is
`∀ā. Q ⇒ τ₀ → τ₁ → τ₂` with the second arrow unrestricted. -/
theorem app_var_arr_omega {k n : Nat} {Γ : Fin n → Scheme P k} {g y : Fin n}
    (hg : ∃ π₀ τ₀ τ₁ τ₂, (Γ g).τ = .arr π₀ τ₀ (.arr .omega τ₁ τ₂)) (Q' : SConstr (Atom P k))
    (u' : Fin n → Usage) (π : Mult) (τ₁ τ₂ : Ty P k)
    (d : HasType D sig Q' Γ u' (.app (.var g) (.var y)) (.arr π τ₁ τ₂)) : π = .omega := by
  obtain ⟨Q₁, Q₂, u₁, u₂, π', τ', hu, ⟨d₁⟩, hd₂⟩ := app_invU d
  obtain ⟨-, τs, h⟩ := var_invU d₁
  exact arr_arr_subst_omega (Γ g) τs hg h

end HasType

-- [NOT IN PAPER ◀ END] usage-tracking inversion lemmas

-- [PAPER ▶ START] Figure 1b / §6.3.2 / Figure 3: a variable bound by `pack` cannot be passed to
--   an unrestricted argument

namespace Mem

open HasType

variable {D : LDomain (Atom Pred)} {sig : DataSig Pred}

/-- `let pack x = e₁ in f x` is ill typed whenever `f` takes its argument unrestrictedly: the
variable `x` bound by `pack` is linear. -/
theorem unpack_then_unrestricted_rejected {k n j : Nat} {Γ : Fin n → Scheme Pred k}
    (e₁ : Tm sig k n) (f : Tm sig (k + j) (n + 1))
    (hf : ∀ (Γ' : Fin (n + 1) → Scheme Pred (k + j)) (Q' : SConstr (Atom Pred (k + j)))
      (u' : Fin (n + 1) → Usage) (π : Mult) (τ₁ τ₂ : Ty Pred (k + j)),
      (∀ i : Fin n, Γ' i.succ = ctxWk j Γ i) →
      HasType D sig Q' Γ' u' f (.arr π τ₁ τ₂) → π = .omega)
    (Q : SConstr (Atom Pred k)) (u : Fin n → Usage) (τ : Ty Pred k) :
    IsEmpty (HasType D sig Q Γ u (.unpack j e₁ (.app f (.var 0))) τ) := by
  refine ⟨fun d => ?_⟩
  obtain ⟨Q₂, u₂, τ₁, ⟨d₂⟩⟩ := unpack_invU d
  have h := app_var_omega (hf _ · · · · · (fun _ => rfl)) d₂
  simp at h

/-- With the type of `new` printed in Figure 1b, `∃ n. UArray a n ⧀ RW n`, the array can only
be reached by `let pack arr = new 10 in …`, which binds it linearly; then `free arr` is ill
typed, since `free :: RW n =⚬ UArray a n -> ()` takes the array unrestrictedly.  This holds for
every expression in place of `new 10`, every given constraint, type and usage. -/
theorem unpack_free_rejected {k n j : Nat} {Γ : Fin n → Scheme Pred k} {fr : Fin n}
    (hfr : ∃ τ₁ τ₂, (Γ fr).τ = .arr .omega τ₁ τ₂)
    (e₁ : Tm sig k n) (Q : SConstr (Atom Pred k)) (u : Fin n → Usage) (τ : Ty Pred k) :
    IsEmpty (HasType D sig Q Γ u (.unpack j e₁ (.app (.var fr.succ) (.var 0))) τ) := by
  refine unpack_then_unrestricted_rejected e₁ _ (fun Γ' Q' u' π τ₁ τ₂ hΓ d => ?_) Q u τ
  refine var_arr_omega ?_ Q' u' π τ₁ τ₂ d
  obtain ⟨a, b, hab⟩ := hfr
  rw [hΓ fr]
  simp only [ctxWk, Scheme.rename, hab, Ty.rename]
  exact ⟨_, _, rfl⟩

/-- `free`'s argument is unrestricted (Figure 1b). -/
lemma freeS_arr : ∃ τ₁ τ₂, freeS.τ = .arr .omega τ₁ τ₂ := ⟨_, _, rfl⟩

/-- `split`'s `Int` argument is unrestricted (§4.2). -/
lemma splitS_arr : ∃ π₀ τ₀ τ₁ τ₂, splitS.τ = .arr π₀ τ₀ (.arr .omega τ₁ τ₂) :=
  ⟨_, _, _, _, rfl⟩

/-- **Figure 1b vs §6.3.2.**  In the context `memΓ` (variable `4` is `free`), with any
expression `newCall` standing for `new 10` at the type of Figure 1b, the program
`let pack arr = newCall in free arr` has no typing derivation. -/
theorem free_after_unpack_rejected (newCall : Tm memSig 0 22) (Q : SConstr (Atom Pred 0))
    (u : Fin 22 → Usage) (τ : Ty Pred 0) :
    IsEmpty (HasType memD memSig Q memΓ u
      (.unpack 1 newCall (.app (.var (4 : Fin 22).succ) (.var 0))) τ) :=
  unpack_free_rejected (fr := 4) freeS_arr newCall Q u τ

/-- **Figure 3 as printed.**  `let pack pivotIdx = partitionCall; pack (Ur (l, r)) = split arr
pivotIdx in rest` is ill typed for every `partitionCall` (standing for `partition arr`), every
continuation `rest`, every given constraint, type and usage: `pivotIdx` is bound linearly by
`pack` and passed to the unrestricted `Int` argument of `split`.  The context is `memΓ` (where
`split` is variable `10`) extended with the array `arr`, and `j₁`, `j₂` are the numbers of type
variables opened by the two unpackings. -/
theorem sort_printed_rejected {j₁ j₂ : Nat} (arrT : Ty Pred 0)
    (partitionCall : Tm memSig 0 23)
    (rest : Tm memSig (0 + j₁ + j₂) 25) (Q : SConstr (Atom Pred 0)) (u : Fin 23 → Usage)
    (τ : Ty Pred 0) :
    IsEmpty (HasType memD memSig Q (Fin.cons (Scheme.mono arrT) memΓ) u
      (.unpack j₁ partitionCall
        (.unpack j₂ (.app (.app (.var (11 : Fin 23).succ) (.var (0 : Fin 23).succ)) (.var 0))
          rest)) τ) := by
  refine ⟨fun d => ?_⟩
  obtain ⟨Q₂, u₂, τ₁, ⟨d₂⟩⟩ := unpack_invU d
  obtain ⟨Q₃, v₁, v₂, τ₃, hv, ⟨d₃⟩⟩ := unpack_invU₁ d₂
  have h := app_var_omega (app_var_arr_omega ⟨_, _, _, _, rfl⟩) d₃
  have h0 := congrFun hv 0
  simp [h] at h0

end Mem

-- [PAPER ◀ END] a variable bound by `pack` cannot be passed to an unrestricted argument

end LQT
