module

public import RequestProject.LH.Semantics

/-!
# Examples of `λq→` (Linear Haskell §3.3 and §3.5)

The examples of the paper, in the formal calculus.  Since `λq→` has no type polymorphism, the
polymorphic examples of the paper are instantiated at a unit type `Unit`.
-/

@[expose] public section

namespace LH.Ex

-- [NOT IN PAPER ▶ START] the datatypes used by the examples
/-- Datatype names. -/
inductive D
  /-- `data Unit where U : Unit` -/
  | unit
  /-- `data Pair where Pair : Unit ⊸ Unit ⊸ Pair` (both fields of a pair are linear, §2.4) -/
  | pair
  /-- `data UrUnit where UrU : Unit →ω UrUnit` (`Unrestricted Unit`) -/
  | urUnit
  /-- `data UrPair where UrP : Pair →ω UrPair` (`Unrestricted Pair`) -/
  | urPair
  /-- `data PairUr where PU : UrUnit ⊸ UrUnit ⊸ PairUr` (pair of `Unrestricted Unit`) -/
  | pairUr
  /-- `data PairPQ p q where PairPQ : Unit →p Unit →q PairPQ p q` (§3.5 "Case rule") -/
  | pairPQ
  deriving DecidableEq

/-- Number of multiplicity parameters. -/
def np : D → Nat
  | .pairPQ => 2
  | _ => 0

/-- Number of fields of the (unique) constructor. -/
def ar : D → Nat
  | .unit => 0
  | .urUnit => 1
  | .urPair => 1
  | _ => 2

/-- `D π⃗` as a type. -/
abbrev dTy {m : Nat} (d : D) (ps : Fin (np d) → Mult m) : Ty D np m := .data d ps

/-- The type `Unit`. -/
abbrev unitTy {m : Nat} : Ty D np m := .data .unit Fin.elim0
/-- The type `Pair`. -/
abbrev pairTy {m : Nat} : Ty D np m := .data .pair Fin.elim0
/-- The type `UrUnit`. -/
abbrev urUnitTy {m : Nat} : Ty D np m := .data .urUnit Fin.elim0
/-- The type `UrPair`. -/
abbrev urPairTy {m : Nat} : Ty D np m := .data .urPair Fin.elim0
/-- The type `PairUr`. -/
abbrev pairUrTy {m : Nat} : Ty D np m := .data .pairUr Fin.elim0

/-- Field types. -/
def fieldTy : (d : D) → Fin (ar d) → Ty D np (np d)
  | .unit, i => i.elim0
  | .pair, _ => unitTy
  | .urUnit, _ => unitTy
  | .urPair, _ => pairTy
  | .pairUr, _ => urUnitTy
  | .pairPQ, _ => unitTy

/-- Field multiplicities. -/
def fieldMult : (d : D) → Fin (ar d) → Mult (np d)
  | .unit, i => i.elim0
  | .pair, _ => 1
  | .urUnit, _ => Mult.omega
  | .urPair, _ => Mult.omega
  | .pairUr, _ => 1
  | .pairPQ, i => Mult.var i

/-- The signature of the examples: every datatype has one constructor. -/
def S : Sig where
  Dn := D
  np := np
  ncons _ := 1
  arity d _ := ar d
  fieldTy d _ := fieldTy d
  fieldMult d _ := fieldMult d

/-- Equalities of closed usage vectors are decided by evaluation in `{0, 1, ω}`. -/
macro "usage_eq" : tactic =>
  `(tactic| (funext x; apply Usage.eval0_injective; revert x; decide))

/-- Every datatype of the examples has a single constructor. -/
theorem con_eq_zero {d : D} (k : Fin (S.ncons d)) : k = ⟨0, Nat.one_pos⟩ :=
  Fin.ext (by have h : k.val < 1 := k.isLt; show k.val = 0; omega)
-- [NOT IN PAPER ◀ END]

-- [PAPER ▶ START] §3.3: `swap :: (a, b) ⊸ (b, a)`, `swap (a, b) = (b, a)` uses `case₁`
/-- `swap = λ₁ (x : Pair). case₁ x of Pair a b → Pair b a`. -/
def swap : Tm S 0 0 :=
  .lam 1 pairTy (.case 1 (.var 0) D.pair (fun _ => .con D.pair (0 : Fin 1) ![.var 2, .var 1]))

/-- `swap : Pair ⊸ Pair`. -/
theorem swap_typed : HasType S Fin.elim0 0 swap (.arr pairTy 1 pairTy) := by
  refine .lam (.case (u₁ := Pi.single 0 1) (u₂ := 0) (ps := Fin.elim0) (.var 0 0 ?_)
    (fun k => ?_) ?_)
  · usage_eq
  · obtain rfl := con_eq_zero k
    refine .con (S := S) (d := D.pair) (k := (0 : Fin 1)) (ps := Fin.elim0) 0
      ![Pi.single 2 1, Pi.single 1 1] (fun i => ?_) ?_
    · fin_cases i
      · exact .var 2 0 (by usage_eq)
      · exact .var 1 0 (by usage_eq)
    · usage_eq
  · usage_eq
-- [PAPER ◀ END]

/-- Types of the examples, compared up to the (irrelevant) arguments of parameterless
datatypes. -/
theorem dTy_eq {m : Nat} {d : D} (a b : Fin (np d) → Mult m) (h : np d = 0) :
    (Ty.data d a : Ty D np m) = Ty.data d b := by
  congr 1; funext i; exact absurd i.isLt (by omega)

theorem subst_unitTyS {m m' : Nat} (s : Fin m → Mult m') :
    @Ty.subst S.Dn S.np m m' s unitTy = unitTy := dTy_eq _ _ rfl

macro "ty_eq" : tactic => `(tactic| exact dTy_eq _ _ rfl)

theorem natAdd_one_ne_zero (n : Nat) : (Fin.natAdd n (1 : Fin 2) : Fin (n + 2)) ≠ Fin.natAdd n 0 := by
  simp [Fin.ext_iff]

-- [PAPER ▶ START] §3.3: `fst :: (a, b) → a`, `fst (a, b) = a` forces `case_ω`
/-- `fst = λ_ω (x : Pair). case_ω x of Pair a b → a`. -/
def fst : Tm S 0 0 :=
  .lam Mult.omega pairTy (.case Mult.omega (.var 0) D.pair (fun _ => .var 1))

/-- `fst : Pair → Unit` (with `case_ω`). -/
theorem fst_typed : HasType S Fin.elim0 0 fst (.arr pairTy Mult.omega unitTy) := by
  refine .lam (.case (u₁ := Pi.single 0 1) (u₂ := 0) (ps := Fin.elim0) (.var 0 0 ?_)
    (fun k => ?_) ?_)
  · usage_eq
  · obtain rfl := con_eq_zero k
    exact .var_of_eq 1 ![0, 1, 1] (by usage_eq) (by ty_eq)
  · usage_eq

/-- With `case₁`, the body of `fst` is ill typed, whatever the scrutinee, the context and the
type: the second field is discarded, but it would be bound linearly. -/
theorem fst_case_one_untypable {m n : Nat} (Γ : Fin n → S.Ty m) (u : Fin n → Usage m)
    (t : Tm S m n) (C : S.Ty m) :
    ¬ HasType S Γ u (.case 1 t D.pair (fun _ => .var (Fin.natAdd n (0 : Fin 2)))) C := by
  intro h
  cases h with
  | case _ hbrs _ =>
    obtain ⟨_, v, hv⟩ := (hbrs ⟨0, Nat.one_pos⟩).var_inv
    have := congrArg (Usage.eval fun _ => V3.one) (congrFun hv (Fin.natAdd n (1 : Fin 2)))
    rw [Pi.add_apply, Pi.single_apply, if_neg (natAdd_one_ne_zero n)] at this
    simp [S, fieldMult] at this
    revert this
    cases Usage.eval (fun _ => V3.one) (v (Fin.natAdd n (1 : Fin 2))) <;> decide

/-- Hence `fst` has no linear type: `λ₁ (x : Pair). case_π x of Pair a b → a` is ill typed for
every multiplicity `π`. -/
theorem fst_linear_untypable {m n : Nat} (Γ : Fin n → S.Ty m) (u : Fin n → Usage m)
    (π : Mult m) (A : S.Ty m) :
    ¬ HasType S Γ u
      (.lam 1 pairTy (.case π (.var 0) D.pair (fun _ => .var (Fin.natAdd (n + 1) (0 : Fin 2))))) A := by
  intro h
  cases h with
  | lam hb =>
    cases hb with
    | @case _ _ _ _ _ u₂ _ _ _ _ _ _ h₁ hbrs hu =>
      obtain ⟨_, v, hv⟩ := h₁.var_inv
      obtain ⟨_, v', hv'⟩ := (hbrs ⟨0, Nat.one_pos⟩).var_inv
      have e₁ := congrArg (Usage.eval fun _ => V3.one) (congrFun hu 0)
      have e₂ := congrArg (Usage.eval fun _ => V3.one) (congrFun hv' (Fin.natAdd (n + 1) (1 : Fin 2)))
      have e₃ := congrArg (Usage.eval fun _ => V3.one) (congrFun hv 0)
      have hπ := Mult.lift_ne_zero (fun _ => V3.one) (fun _ h => by cases h) π
      rw [Pi.add_apply, Pi.single_apply, if_neg (natAdd_one_ne_zero (n + 1))] at e₂
      simp [S, fieldMult] at e₁ e₂ e₃
      rw [e₃] at e₁
      revert e₁ e₂ hπ
      cases Mult.lift (fun _ => V3.one) π <;>
        cases Usage.eval (fun _ => V3.one) (v 0) <;>
        cases Usage.eval (fun _ => V3.one) (v' (Fin.natAdd (n + 1) (1 : Fin 2))) <;>
        cases Usage.eval (fun _ => V3.one) (u₂ 0) <;> decide
-- [PAPER ◀ END]

-- [PAPER ▶ START] §3.5 "Case rule": `fst :: Pair 1 ω a b ⊸ a`, `fst x = case₁ x of Pair a b → a`
/-- `fstPQ = λ₁ (x : PairPQ 1 ω). case₁ x of PairPQ a b → a`. -/
def fstPQ : Tm S 0 0 :=
  .lam 1 (dTy D.pairPQ ![1, Mult.omega]) (.case 1 (.var 0) D.pairPQ (fun _ => .var 1))

/-- With multiplicity-polymorphic pairs, `fst` gets a linear type using `case₁`. -/
theorem fstPQ_typed :
    HasType S Fin.elim0 0 fstPQ (.arr (dTy D.pairPQ ![1, Mult.omega]) 1 unitTy) := by
  refine .lam (.case (u₁ := Pi.single 0 1) (u₂ := 0) (ps := ![1, Mult.omega]) (.var 0 0 ?_)
    (fun k => ?_) ?_)
  · usage_eq
  · obtain rfl := con_eq_zero k
    exact .var_of_eq 1 ![0, 0, 1] (by usage_eq) (by ty_eq)
  · usage_eq
-- [PAPER ◀ END]

-- [PAPER ▶ START] §3.5 "Case rule": `case_ω` inhabits
--   `∀ a b. Unrestricted (a, b) ⊸ (Unrestricted a, Unrestricted b)`
/-- `λ₁ (x : UrPair). case₁ x of UrP p → case_ω p of Pair a b → PU (UrU a) (UrU b)`. -/
def unzipUr : Tm S 0 0 :=
  .lam 1 urPairTy (.case 1 (.var 0) D.urPair (fun _ =>
    .case Mult.omega (.var 1) D.pair (fun _ =>
      .con D.pairUr (0 : Fin 1) ![.con D.urUnit (0 : Fin 1) ![.var 2],
        .con D.urUnit (0 : Fin 1) ![.var 3]])))

/-- `unzipUr : Unrestricted Pair ⊸ (Unrestricted Unit, Unrestricted Unit)`. -/
theorem unzipUr_typed : HasType S Fin.elim0 0 unzipUr (.arr urPairTy 1 pairUrTy) := by
  refine .lam (.case (u₁ := Pi.single 0 1) (u₂ := 0) (ps := Fin.elim0) (.var 0 0 ?_)
    (fun k => ?_) ?_)
  · usage_eq
  · obtain rfl := con_eq_zero k
    refine .case (u₁ := Pi.single 1 1) (u₂ := 0) (ps := Fin.elim0) (.var_of_eq 1 0 ?_ ?_)
      (fun k => ?_) ?_
    · usage_eq
    · ty_eq
    · obtain rfl := con_eq_zero k
      refine .con (S := S) (d := D.pairUr) (k := (0 : Fin 1)) (ps := Fin.elim0) 0
        ![![0, 0, Usage.omega, 0], ![0, 0, 0, Usage.omega]] (fun i => ?_) ?_
      · fin_cases i
        · refine .con (S := S) (d := D.urUnit) (k := (0 : Fin 1)) 0 ![Pi.single 2 1]
            (fun i => ?_) ?_
          · fin_cases i
            exact .var_of_eq 2 0 (by usage_eq) (by ty_eq)
          · usage_eq
        · refine .con (S := S) (d := D.urUnit) (k := (0 : Fin 1)) 0 ![Pi.single 3 1]
            (fun i => ?_) ?_
          · fin_cases i
            exact .var_of_eq 3 0 (by usage_eq) (by ty_eq)
          · usage_eq
      · usage_eq
    · usage_eq
  · usage_eq
-- [PAPER ◀ END]

-- [PAPER ▶ START] §3.5 "Polymorphism & multiplicities": `id x = x`
/-- `id₁ = λ₁ (x : Unit). x : Unit ⊸ Unit`. -/
theorem id_linear_typed :
    HasType S (Fin.elim0 : Fin 0 → S.Ty 0) 0 (.lam 1 unitTy (.var 0)) (.arr unitTy 1 unitTy) :=
  .lam (.var 0 0 (by usage_eq))

/-- `id_ω = λ_ω (x : Unit). x : Unit → Unit`. -/
theorem id_unrestricted_typed :
    HasType S (Fin.elim0 : Fin 0 → S.Ty 0) 0 (.lam Mult.omega unitTy (.var 0))
      (.arr unitTy Mult.omega unitTy) :=
  .lam (.var 0 ![1] (by usage_eq))

/-- But, as the paper says, `id :: ∀p. Int →_p Int` is **not** accepted:
`λp. λ_p (x : Unit). x` has no type, in any context. -/
theorem id_poly_untypable {m n : Nat} (Γ : Fin n → S.Ty m) (u : Fin n → Usage m) (A : S.Ty m) :
    ¬ HasType S Γ u (.mlam (.lam (Mult.var 0) unitTy (.var 0))) A := by
  intro h
  cases h with
  | mlam hb =>
    cases hb with
    | lam hb' =>
      obtain ⟨_, v, hv⟩ := hb'.var_inv
      have := congrArg (Usage.eval fun _ => V3.zero) (congrFun hv 0)
      simp only [Fin.cons_zero, Pi.add_apply, Pi.smul_apply, smul_eq_mul, map_add, map_mul,
        Usage.eval_nz, Pi.single_eq_same, Mult.lift_var, map_one, Usage.eval_omega] at this
      revert this
      cases Usage.eval (fun _ => V3.zero) (v 0) <;> decide
-- [PAPER ◀ END]

-- [PAPER ▶ START] §3.5 "Subtyping": with `f :: Int ⊸ Int` and `g :: (Int → Int) → Bool`, `g f` is
--   ill typed, its η-expansion is well typed, and so is `g f` for a multiplicity-polymorphic `g`
/-- The context `f : Unit ⊸ Unit, g : (Unit → Unit) → Unit` (`f` is variable `0`). -/
def ΓSub : Fin 2 → S.Ty 0 :=
  ![.arr unitTy 1 unitTy, .arr (.arr unitTy Mult.omega unitTy) Mult.omega unitTy]

/-- `g f` is ill typed: `λq→` has no subtyping. -/
theorem subtyping_rejected (u : Fin 2 → Usage 0) (B : S.Ty 0) :
    ¬ HasType S ΓSub u (.app (.var 1) (.var 0)) B := by
  intro h
  obtain ⟨_, _, _, A, h₁, h₂, _⟩ := h.app_inv
  obtain ⟨e₁, _⟩ := h₁.var_inv
  obtain ⟨e₂, _⟩ := h₂.var_inv
  simp only [ΓSub, Matrix.cons_val_one, Matrix.cons_val_zero] at e₁ e₂
  subst e₂
  simp only [Ty.arr.injEq] at e₁
  exact Mult.one_ne_omega e₁.1.2.1

/-- The η-expansion `g (λ_ω (x : Unit). f x)` is well typed. -/
theorem subtyping_eta_typed :
    HasType S ΓSub ![Usage.omega, 1]
      (.app (.var 1) (.lam Mult.omega unitTy (.app (.var 1) (.var 0)))) unitTy := by
  refine .app (u₁ := Pi.single 1 1) (u₂ := Pi.single 0 1) (.var 1 0 (by usage_eq))
    (.lam (.app (u₁ := ![Usage.omega, 1, 0]) (u₂ := Pi.single 0 1) (.var 1 ![1, 0, 0] (by usage_eq))
      (.var 0 0 (by usage_eq)) (by usage_eq))) (by usage_eq)

/-- The context `f : Unit ⊸ Unit, g : ∀p. (Unit →_p Unit) → Unit`. -/
def ΓPoly : Fin 2 → S.Ty 0 :=
  ![.arr unitTy 1 unitTy, .all (.arr (.arr unitTy (Mult.var 0) unitTy) Mult.omega unitTy)]

/-- With a multiplicity-polymorphic `g`, `g 1 f` is well typed. -/
theorem subtyping_poly_typed :
    HasType S ΓPoly ![Usage.omega, 1] (.app (.mapp (.var 1) 1) (.var 0)) unitTy := by
  refine .app (u₁ := Pi.single 1 1) (u₂ := Pi.single 0 1) (A := .arr unitTy 1 unitTy)
    (π := Mult.omega) ?_ (.var 0 0 (by usage_eq)) (by usage_eq)
  have := HasType.mapp (π := 1) (HasType.var (S := S) (Γ := ΓPoly) 1 0
    (u := Pi.single 1 1) (by usage_eq))
  have e : Ty.subst (Fin.cons 1 Mult.var)
      (.arr (.arr unitTy (Mult.var 0) unitTy) Mult.omega unitTy : S.Ty 1) =
      .arr (.arr unitTy 1 unitTy) Mult.omega unitTy := by
    rw [Ty.subst, Ty.subst, Mult.subst_var, Fin.cons_zero, Mult.subst_omega]
    simp only [subst_unitTyS]
  rw [e] at this
  exact this
-- [PAPER ◀ END]

-- [PAPER ▶ START] §2.2 "Safe mutable arrays": `array size pairs = newMArray size (λma -> freeze
--   (foldl write ma pairs))` with `write :: MArray a ⊸ (Int, a) -> MArray a` and
--   `foldl :: (a ⊸ b ⊸ a) -> a ⊸ [b] ⊸ a`
/-- A function whose argument is unrestricted cannot be η-expanded into a linear function:
if `f : A → B` then `λ₁ (y : A). f y` is ill typed, in any context and at any type.  So the
instance `foldl :: (a ⊸ b ⊸ a) -> a ⊸ [b] ⊸ a` printed in §2.2 cannot be applied to
`write :: MArray a ⊸ (Int, a) -> MArray a`, even with the η-expansion of §3.5 (a suitable
instance of the multiplicity-polymorphic `foldl` of §2.6 is needed instead). -/
theorem eta_linear_of_unrestricted_untypable {S : Sig} {m n : Nat} (Γ : Fin n → S.Ty m)
    (u : Fin n → Usage m) (f : Fin n) (A B C : S.Ty m) (hf : Γ f = .arr A Mult.omega B) :
    ¬ HasType S Γ u (.lam 1 A (.app (.var f.succ) (.var 0))) C := by
  intro h
  cases h with
  | lam hb =>
    obtain ⟨u₁, u₂, π, A', h₁, h₂, hu⟩ := hb.app_inv
    obtain ⟨e₁, -⟩ := h₁.var_inv
    obtain ⟨-, v, hv⟩ := h₂.var_inv
    rw [Fin.cons_succ, hf] at e₁
    simp only [Ty.arr.injEq] at e₁
    obtain ⟨-, rfl, -⟩ := e₁
    have := congrArg (Usage.eval fun _ => V3.one) (congrFun hu 0)
    rw [hv] at this
    simp at this
    revert this
    cases Usage.eval (fun _ => V3.one) (u₁ 0) <;> cases Usage.eval (fun _ => V3.one) (v 0) <;>
      decide
-- [PAPER ◀ END]

-- [PAPER ▶ START] §2.6 "Multiplicity polymorphism":
--   `(◦) :: ∀p q. (b →p c) ⊸ (a →q b) →p a →p·q c`, `(f ◦ g) x = f (g x)`
/-- `compose = λp. λq. λ₁ (f : Unit →_p Unit). λ_p (g : Unit →_q Unit). λ_{p·q} (x : Unit).
f (g x)` (`p` is the multiplicity variable `1` and `q` the variable `0`). -/
def compose : Tm S 0 0 :=
  .mlam (.mlam (.lam 1 (.arr unitTy (Mult.var 1) unitTy)
    (.lam (Mult.var 1) (.arr unitTy (Mult.var 0) unitTy)
      (.lam (Mult.var 1 * Mult.var 0) unitTy (.app (.var 2) (.app (.var 1) (.var 0)))))))

/-- `compose : ∀p q. (Unit →_p Unit) ⊸ (Unit →_q Unit) →_p Unit →_{p·q} Unit`. -/
theorem compose_typed :
    HasType S Fin.elim0 0 compose
      (.all (.all (.arr (.arr unitTy (Mult.var 1) unitTy) 1
        (.arr (.arr unitTy (Mult.var 0) unitTy) (Mult.var 1)
          (.arr unitTy (Mult.var 1 * Mult.var 0) unitTy))))) := by
  refine .mlam (.mlam (.lam (.lam (.lam (.app (u₁ := Pi.single 2 1)
    (u₂ := Pi.single 1 1 + Usage.nz (Mult.var 0) • Pi.single 0 1) (.var 2 0 ?_)
    (.app (u₁ := Pi.single 1 1) (u₂ := Pi.single 0 1) (.var 1 0 ?_) (.var 0 0 ?_) rfl) ?_)))))
  · simp
  · simp
  · simp
  · funext i
    fin_cases i <;> simp [Fin.ext_iff]
    rfl
-- [PAPER ◀ END]

end LH.Ex
