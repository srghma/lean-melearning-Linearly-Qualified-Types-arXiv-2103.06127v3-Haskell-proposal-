module

public import RequestProject.LQT.Ch3_LinearConstraints.ExampleSetting
public import RequestProject.LQT.Ch5_QualifiedTypeSystem.TypingInv
public import RequestProject.LQT.Ch6_ConstraintInference.GenerationInv
public import RequestProject.LQT.Ch6_ConstraintInference.AtomicSolverProps

/-!
# Restricting to a linear context with `Linearly` (§3.2)

Paper location: §3.2 "Restricting to a linear context with `Linearly`" (the programs `bad`,
`badToo`, and the creation of two arrays from one linear `Linearly` assumption).  The start and
end of each part is marked by `-- [PAPER ▶ START]` / `-- [PAPER ◀ END]` comments.

The examples use `new :: Linearly ⊸ Int → MArray`, in the stripped-down domain of Figure 10a in
which `Linearly` is duplicable.  These examples start from the linear `Linearly` assumption that
the `linearly` primitive provides; the primitive itself (whose argument has a qualified type) is
modelled, through an encoding of its argument as a function from evidence, in
`Ch4_MemoryOwnership/Linearly.lean`.

* `badToo_rejected`, `badToo_not_inferred`: `badToo = Ur (new 5)` is rejected by the type system
  and by inference;
* `twoArrays_typed`, `twoArrays_inferred`: two arrays can be created from one linear `Linearly`;
* `bad_not_inferred`: `bad = let arr = new 5 in (arr, arr)` is rejected by inference, for both
  multiplicities of the `let`;
* `bad_omega_typed`: but `bad` is accepted by the declarative type system when `arr` is
  unrestricted (a discrepancy with the paper's text; see the README).
-/

@[expose] public section

namespace LQT

namespace Examples

-- [PAPER ▶ START] §3.2 "Restricting to a linear context with `Linearly`": the setting

/-- The domain of the `Linearly` examples: the stripped-down domain of Figure 10a in which the
(single) atomic constraint is the duplicable `𝓛` (`Linearly`); we reuse `cAtom` for `𝓛` and
`givenC` for the linear assumption `1·𝓛`. -/
def linD : LDomain (Atom Unit) := predLDomain Set.univ

/-- Number of type parameters: `Int` (`0`), `MArray` (`1`), pairs (`2`), `Ur` (`3`). -/
def lnParams : Nat → Nat
  | 2 => 2
  | 3 => 1
  | _ => 0

/-- Number of constructors: `Int` has one literal, `MArray` is abstract, pairs have `(,)`,
`Ur` has `Ur`. -/
def lnNcons : Nat → Nat
  | 0 => 1
  | 2 => 1
  | 3 => 1
  | _ => 0

/-- Number of fields of the constructors. -/
def lnArity : (T : Nat) → Fin (lnNcons T) → Nat
  | 2, _ => 2
  | 3, _ => 1
  | _, _ => 0

/-- Fields: the pair constructor has two linear fields, `Ur` has one unrestricted field. -/
def lnField : (T : Nat) → (i : Fin (lnNcons T)) → Fin (lnArity T i) → Mult × Ty Unit (lnParams T)
  | 0, _, l => l.elim0
  | 1, i, _ => i.elim0
  | 2, _, l => (.one, .tvar l)
  | 3, _, _ => (.omega, .tvar (⟨0, by decide⟩ : Fin 1))
  | _ + 4, i, _ => i.elim0

/-- The data type signature of the `Linearly` examples. -/
def lnSig : DataSig Unit := ⟨lnParams, lnNcons, lnArity, lnField⟩

/-- The type `MArray` (abstract). -/
def arrTy {k : Nat} : Ty Unit k := .data 1 0 (fun l => l.elim0)

/-- The pair type `(a, b)`. -/
def pairTy {k : Nat} (a b : Ty Unit k) : Ty Unit k := .data 2 2 ![a, b]

/-- The scheme of `new :: Linearly ⊸ Int → MArray`. -/
def newScheme : Scheme Unit 0 := ⟨0, givenC, .arr .omega intTy arrTy⟩

/-- The context: `new` (index `0`). -/
def lnΓ : Fin 1 → Scheme Unit 0 := ![newScheme]

/-- An integer literal. -/
def lit {n : Nat} : Tm lnSig 0 n := .con 0 ⟨0, by decide⟩

/-- The pair `(a, b)`. -/
def pairE {n : Nat} (a b : Tm lnSig 0 n) : Tm lnSig 0 n := .app (.app (.con 2 ⟨0, by decide⟩) a) b

/-- `bad = let_π arr = new 5 in (arr, arr)`. -/
def bad (π : Mult) : Tm lnSig 0 1 := .let_ π (.app (.var 0) lit) (pairE (.var 0) (.var 0))

/-- `badToo = Ur (new 5)`. -/
def badToo : Tm lnSig 0 1 := .app (.con 3 ⟨0, by decide⟩) (.app (.var 0) lit)

/-- `let_1 arr1 = new 5 in let_1 arr2 = new 6 in (arr1, arr2)`. -/
def twoArrays : Tm lnSig 0 1 :=
  .let_ .one (.app (.var 0) lit) (.let_ .one (.app (.var 1) lit) (pairE (.var 1) (.var 0)))

-- [PAPER ◀ END] §3.2, the setting

-- [NOT IN PAPER ▶ START] helpers for the `Linearly` examples

lemma linD_lawful : ∀ k, (linD k).Lawful := (predLDomain_lawful Set.univ).lawful

/-- In the domain `linD`, a constraint with no copy of `𝓛` entails only constraints with no copy
of `𝓛`. -/
lemma lin_ent {k : Nat} {Q R : SConstr (Atom Unit k)} (h : (linD k).Entails Q R)
    (hU : cAtom ∉ Q.U) (hL : Q.L.count cAtom = 0) : cAtom ∉ R.U ∧ R.L.count cAtom = 0 := by
  obtain ⟨hU', -, hD⟩ := h
  refine ⟨fun h' => hU (hU' h'), ?_⟩
  by_contra hne
  rcases hD cAtom (Set.mem_univ _) (Nat.pos_of_ne_zero hne) with h' | h'
  · exact hU h'
  · omega

@[simp] lemma arrTy_subst {k k' : Nat} (σ : Fin k → Ty Unit k') :
    (arrTy : Ty Unit k).subst σ = arrTy := by
  simp only [arrTy, Ty.subst]
  congr 1; funext l; exact l.elim0

@[simp] lemma SConstr.tsubst_zero' {k k' : Nat} (σ : Fin k → Ty Unit k') :
    (0 : SConstr (Atom Unit k)).tsubst σ = 0 := by
  simp [SConstr.tsubst]

/-- Recasting a typing derivation along an equality of usages. -/
noncomputable def castU {k n : Nat} {Q : SConstr (Atom Unit k)} {Γ : Fin n → Scheme Unit k}
    {u u' : Fin n → Usage} {e : Tm lnSig k n} {τ : Ty Unit k} (h : u = u')
    (d : HasType linD lnSig Q Γ u e τ) : HasType linD lnSig Q Γ u' e τ := h ▸ d

/-- `new 5 : MArray`, consuming `1·𝓛`, where `new` is the variable `x`. -/
noncomputable def newApp_typed {n : Nat} {Γ : Fin n → Scheme Unit 0} {x : Fin n} (hx : Γ x = newScheme) :
    HasType linD lnSig givenC Γ (single x) (.app (.var x) lit) arrTy := by
  have d₁ := HasType.var (D := linD) (sig := lnSig) (Γ := Γ) (x := x) (σ := newScheme) 0
    Fin.elim0 hx
  have d₂ := HasType.con (D := linD) (sig := lnSig) (Γ := Γ) 0 0 ⟨0, by decide⟩ Fin.elim0
  have e₂ : (lnSig.conTy 0 ⟨0, by decide⟩).subst (Fin.elim0 : Fin (lnSig.params 0) → Ty Unit 0)
      = intTy := by
    simp only [DataSig.conTy, lnSig, intTy]
    congr 1
  simp only [newScheme, Ty.subst, intTy_subst, arrTy_subst] at d₁
  rw [e₂] at d₂
  refine castU ?_ (.sub (.app d₁ d₂) ((linD_lawful 0).entails_of_eq ?_))
  · funext i; simp [single]
  · simp

/-- The pair `(a, b)`. -/
noncomputable def pair_typed {n : Nat} {Γ : Fin n → Scheme Unit 0} {Q₁ Q₂ : SConstr (Atom Unit 0)}
    {u₁ u₂ : Fin n → Usage} {a b : Tm lnSig 0 n} {τa τb : Ty Unit 0}
    (d₁ : HasType linD lnSig Q₁ Γ u₁ a τa) (d₂ : HasType linD lnSig Q₂ Γ u₂ b τb) :
    HasType linD lnSig (Q₁ + Q₂) Γ (u₁ + u₂) (pairE a b) (pairTy τa τb) := by
  have d₀ := HasType.con (D := linD) (sig := lnSig) (Γ := Γ) 0 2 ⟨0, by decide⟩ ![τa, τb]
  have e₀ : (lnSig.conTy 2 ⟨0, by decide⟩).subst ![τa, τb] =
      .arr .one τa (.arr .one τb (pairTy τa τb)) := by
    simp only [DataSig.conTy, lnSig, arrows, lnField, lnArity, Ty.subst, pairTy]
    rfl
  rw [e₀] at d₀
  refine castU ?_ (.sub (.app (.app d₀ d₁) d₂) ((linD_lawful 0).entails_of_eq ?_))
  · funext i; simp
  · simp

/-- A variable of type `Q ⇒ MArray` (no type variables). -/
noncomputable def varArr_typed {n : Nat} {Γ : Fin n → Scheme Unit 0} {x : Fin n}
    {Q : SConstr (Atom Unit (0 + 0))} (hx : Γ x = ⟨0, Q, arrTy⟩) :
    HasType linD lnSig (Q.tsubst (instSub Fin.elim0)) Γ (single x) (.var x) arrTy := by
  have d := HasType.var (D := linD) (sig := lnSig) (Γ := Γ) (x := x) (σ := ⟨0, Q, arrTy⟩) 0
    Fin.elim0 hx
  simp only [arrTy_subst] at d
  exact castU (by funext i; simp) d

lemma genCast {k n : Nat} {Γ : Fin n → Scheme Unit k} {u u' : Fin n → Usage}
    {e : Tm lnSig k n} {τ : Ty Unit k} {C C' : Wanted (Atom Unit) k}
    (g : Gen lnSig Γ u e τ C) (hu : u = u') (hC : C = C') : Gen lnSig Γ u' e τ C' := by
  subst hu hC; exact g

lemma genNewApp {n : Nat} {Γ : Fin n → Scheme Unit 0} {x : Fin n} (hx : Γ x = newScheme) :
    Gen lnSig Γ (single x) (.app (.var x) lit) arrTy (.tensor (.simple givenC) (.simple 0)) := by
  have g₁ := Gen.var (sig := lnSig) (Γ := Γ) (x := x) (σ := newScheme) 0 Fin.elim0 hx
  have g₂ := Gen.con (sig := lnSig) (Γ := Γ) 0 0 ⟨0, by decide⟩ Fin.elim0
  have e₂ : (lnSig.conTy 0 ⟨0, by decide⟩).subst (Fin.elim0 : Fin (lnSig.params 0) → Ty Unit 0)
      = intTy := by
    simp only [DataSig.conTy, lnSig, intTy]
    congr 1
  simp only [newScheme, Ty.subst, intTy_subst, arrTy_subst] at g₁
  rw [e₂] at g₂
  refine genCast (Gen.app g₁ g₂) ?_ ?_
  · funext i; simp [single]
  · simp

lemma genPair {n : Nat} {Γ : Fin n → Scheme Unit 0} {u₁ u₂ : Fin n → Usage}
    {a b : Tm lnSig 0 n} {τa τb : Ty Unit 0} {C₁ C₂ : Wanted (Atom Unit) 0}
    (g₁ : Gen lnSig Γ u₁ a τa C₁) (g₂ : Gen lnSig Γ u₂ b τb C₂) :
    Gen lnSig Γ (u₁ + u₂) (pairE a b) (pairTy τa τb) (.tensor (.tensor (.simple 0) C₁) C₂) := by
  have g₀ := Gen.con (sig := lnSig) (Γ := Γ) 0 2 ⟨0, by decide⟩ ![τa, τb]
  have e₀ : (lnSig.conTy 2 ⟨0, by decide⟩).subst ![τa, τb] =
      .arr .one τa (.arr .one τb (pairTy τa τb)) := by
    simp only [DataSig.conTy, lnSig, arrows, lnField, lnArity, Ty.subst, pairTy]
    rfl
  rw [e₀] at g₀
  refine genCast (Gen.app (Gen.app g₀ g₁) g₂) ?_ ?_
  · funext i; simp
  · simp

lemma genVarArr {n : Nat} {Γ : Fin n → Scheme Unit 0} {x : Fin n}
    {Q : SConstr (Atom Unit (0 + 0))} (hx : Γ x = ⟨0, Q, arrTy⟩) :
    Gen lnSig Γ (single x) (.var x) arrTy (.simple (Q.tsubst (instSub Fin.elim0))) := by
  have g := Gen.var (sig := lnSig) (Γ := Γ) (x := x) (σ := ⟨0, Q, arrTy⟩) 0 Fin.elim0 hx
  simp only [arrTy_subst] at g
  exact genCast g (by funext i; simp) rfl


-- [NOT IN PAPER ◀ END] helpers

-- [PAPER ▶ START] §3.2: "the use of `Ur` in `badToo` requires using the `Linearly` assumption ω
--   times"; "If `Linearly` is assumed linearly, then `let arr1 = new 5; arr2 = new 6` will fail
--   ... We thus stipulate that `Linearly` must itself be duplicable"; "our definition for `bad` is
--   rejected: either we infer `arr` to have multiplicity ω, in which case its definition uses
--   `Linearly` ω times; or we infer `arr` to have multiplicity 1, in which case its use (twice)
--   violates the linearity restriction."

/-- `badToo = Ur (new 5)` is rejected under the linear assumption `1·𝓛`, at every type and
usage. -/
theorem badToo_rejected (u : Fin 1 → Usage) (τ : Ty Unit 0) :
    IsEmpty (HasType linD lnSig givenC lnΓ u badToo τ) := by
  refine ⟨fun d => ?_⟩
  obtain ⟨Q₁, Q₂, u₁, u₂, π, τ₁, h, ⟨d₁⟩, ⟨d₂⟩⟩ := HasType.app_inv linD_lawful d
  obtain ⟨τs, -, hty⟩ := HasType.con_inv linD_lawful d₁
  simp [DataSig.conTy, lnSig, arrows, lnField, lnArity, Ty.subst] at hty
  obtain ⟨rfl, -⟩ := hty
  obtain ⟨Q₂₁, Q₂₂, u₂₁, u₂₂, π', τ', h₂, ⟨d₂₁⟩, -⟩ := HasType.app_inv linD_lawful d₂
  obtain ⟨τs', h₂₁, -⟩ := HasType.var_inv linD_lawful d₂₁
  change (linD 0).Entails Q₂₁ (SConstr.tsubst _ givenC) at h₂₁
  rw [givenC_tsubst] at h₂₁
  have hU : (Q₁ + (Mult.omega : Mult) • Q₂).U ⊆ ∅ := h.1
  simp only [SConstr.add_U, SConstr.omega_smul_U, Finset.subset_empty, Finset.union_eq_empty,
    Multiset.toFinset_eq_empty] at hU
  obtain ⟨-, hQ₂U, hQ₂L⟩ := hU
  obtain ⟨hU₂, hL₂⟩ := lin_ent h₂ (by simp [hQ₂U]) (by simp [hQ₂L])
  simp only [SConstr.add_U, Finset.mem_union, not_or, SConstr.add_L, Multiset.count_add] at hU₂ hL₂
  obtain ⟨-, hc⟩ := lin_ent h₂₁ hU₂.1 (by omega)
  simp at hc

/-- Consequently (by the soundness of inference, Lemmas 6.4 and 6.5) `badToo` is also rejected
by the inference algorithm. -/
theorem badToo_not_inferred (u : Fin 1 → Usage) (τ : Ty Unit 0) (W : Wanted (Atom Unit) 0)
    (hG : Gen lnSig lnΓ u badToo τ W) :
    ¬ Solve linD (fun _ => simpleSolver cAtom) ∅ [cAtom] [] W [] := by
  intro hS
  have h := (predLDomain_lawful Set.univ).infer_sound
    (fun k => simpleSolver_sound ((predLDomain_lawful Set.univ).lawful k) cAtom) hG
    (fun _ _ => Set.mem_univ _) hS
  have e : (⟨∅, ((([cAtom] : List (Atom Unit 0)) : Multiset (Atom Unit 0)) +
      (([] : List (Atom Unit 0)) : Multiset (Atom Unit 0)))⟩ :
      SConstr (Atom Unit 0)) = givenC := by
    ext <;> simp [givenC]
  rw [e] at h
  obtain ⟨d⟩ := h
  exact (badToo_rejected u τ).false d

/-- Thanks to the duplicability of `𝓛`, two arrays can be created from one linear `1·𝓛`. -/
theorem twoArrays_typed : ∃ u : Fin 1 → Usage,
    Nonempty (HasType linD lnSig givenC lnΓ u twoArrays (pairTy arrTy arrTy)) := by
  have hL := linD_lawful 0
  let Γ₂ : Fin 2 → Scheme Unit 0 := Fin.cons ⟨0, 0, arrTy⟩ lnΓ
  let Γ₃ : Fin 3 → Scheme Unit 0 := Fin.cons ⟨0, 0, arrTy⟩ Γ₂
  have body := pair_typed (varArr_typed (Γ := Γ₃) (x := 1) rfl)
    (varArr_typed (Γ := Γ₃) (x := 0) rfl)
  have hb : (single 1 + single 0 : Fin 3 → Usage) =
      Fin.cons (Usage.ofMult .one) (single 0) := by
    funext i; fin_cases i <;> rfl
  have e₁' : HasType linD lnSig (givenC + 0) Γ₂ (single 1) (.app (.var 1) lit) arrTy :=
    .sub (newApp_typed (Γ := Γ₂) (x := 1) rfl) (hL.entails_of_eq (add_zero _))
  have inner := HasType.let_ (Q := 0) (π := .one) e₁' (castU hb body)
  have hi : ((Mult.one : Mult) • single 1 + single 0 : Fin 2 → Usage) =
      Fin.cons (Usage.ofMult .one) (single 0) := by
    funext i; fin_cases i <;> rfl
  have e₁ : HasType linD lnSig (givenC + 0) lnΓ (single 0) (.app (.var 0) lit) arrTy :=
    .sub (newApp_typed (Γ := lnΓ) (x := 0) rfl) (hL.entails_of_eq (add_zero _))
  have outer := HasType.let_ (Q := 0) (π := .one) e₁ (castU hi inner)
  refine ⟨_, ⟨.sub outer ?_⟩⟩
  exact hL.trans (hL.dup_dup (fun _ _ => Set.mem_univ _)) (hL.entails_of_eq (by simp))

/-- The inference algorithm accepts `twoArrays` too: the solver dispatches both demands of
`𝓛` with rule `Atom_OneD`. -/
theorem twoArrays_inferred : ∃ (u : Fin 1 → Usage) (W : Wanted (Atom Unit) 0),
    Gen lnSig lnΓ u twoArrays (pairTy arrTy arrTy) W ∧
      Solve linD (fun _ => simpleSolver cAtom) ∅ [cAtom] [] W [] := by
  let Γ₂ : Fin 2 → Scheme Unit 0 := Fin.cons (Scheme.mono arrTy) lnΓ
  let Γ₃ : Fin 3 → Scheme Unit 0 := Fin.cons (Scheme.mono arrTy) Γ₂
  have body := genPair (genVarArr (Γ := Γ₃) (x := 1) rfl) (genVarArr (Γ := Γ₃) (x := 0) rfl)
  have hb : (single 1 + single 0 : Fin 3 → Usage) =
      Fin.cons (Usage.ofMult .one) (single 0) := by
    funext i; fin_cases i <;> rfl
  have inner := Gen.let_ (π := .one) (genNewApp (Γ := Γ₂) (x := 1) rfl) (genCast body hb rfl)
  have hi : ((Mult.one : Mult) • single 1 + single 0 : Fin 2 → Usage) =
      Fin.cons (Usage.ofMult .one) (single 0) := by
    funext i; fin_cases i <;> rfl
  have g := Gen.let_ (π := .one) (genNewApp (Γ := lnΓ) (x := 0) rfl) (genCast inner hi rfl)
  refine ⟨_, _, g, ?_⟩
  simp only [Wanted.one_smul, SConstr.tsubst_zero']
  have h₀ : simpleSolver cAtom (∅ : Finset (Atom Unit 0)) ([] ++ [cAtom]) [] .one cAtom [] :=
    simpleSolver.oneD (by simp)
  have hA : Solve linD (fun _ => simpleSolver cAtom) ∅ [cAtom] []
      (.tensor (.simple givenC) (.simple 0)) [] :=
    .mult (Solve.atom h₀) .empty
  exact .mult hA (.mult hA (.mult (.mult .empty .empty) .empty))

/-- `bad` is rejected by the inference algorithm, whatever the multiplicity `π` of the binding:
for `π = 1` constraint generation fails (the linear `arr` is used twice), and for `π = ω` the
generated constraint, which contains `ω·𝓛`, cannot be solved from the linear `1·𝓛`. -/
theorem bad_not_inferred (π : Mult) (u : Fin 1 → Usage) (τ : Ty Unit 0)
    (W : Wanted (Atom Unit) 0) (hG : Gen lnSig lnΓ u (bad π) τ W) :
    ¬ Solve linD (fun _ => simpleSolver cAtom) ∅ [cAtom] [] W [] := by
  intro hS
  obtain ⟨u₁, u₂, τ₁, C₁, C₂, -, rfl, g₁, g₂⟩ := genLet_inv hG
  -- the body `(arr, arr)` uses `arr` twice, so `arr` must be unrestricted
  obtain ⟨ua, ub, π₁, τb, Ca, Cb, hu, -, ga, gb⟩ := genApp_inv g₂
  obtain ⟨vb, -, hub, -, -⟩ := genVar_inv gb
  obtain ⟨uc, ud, π₂, τd, Cc, Cd, hua, -, gc, gd⟩ := genApp_inv ga
  obtain ⟨vd, -, hud, -, -⟩ := genVar_inv gd
  obtain ⟨vc, τsc, huc, hty, -⟩ := genCon_inv gc
  simp [DataSig.conTy, lnSig, arrows, lnField, lnArity, Ty.subst] at hty
  obtain ⟨rfl, -, rfl, -⟩ := hty
  have h0 := congrFun hu 0
  rw [hua, huc, hud, hub] at h0
  simp only [Fin.cons_zero, Pi.add_apply, Pi.smul_apply, single, if_true] at h0
  generalize vb 0 = a at h0
  generalize vc 0 = b at h0
  generalize vd 0 = c at h0
  cases π with
  | one => cases a <;> cases b <;> cases c <;> exact absurd h0 (by decide)
  | omega =>
    -- the definition of `arr` then needs `ω·𝓛`, which the linear `𝓛` cannot provide
    obtain ⟨uv, uk, π₃, τk, Cv, Ck, -, rfl, gv, -⟩ := genApp_inv g₁
    obtain ⟨vv, τs, -, -, rfl⟩ := genVar_inv gv
    cases hS with
    | mult h₁ _ =>
      simp only [Wanted.smul_tensor, Wanted.smul_simple] at h₁
      cases h₁ with
      | mult h₁₁ _ =>
        have hU := solve_simple_U linD (fun _ => cAtom) h₁₁ _ rfl
        change (Mult.omega • SConstr.tsubst _ givenC).U ⊆ ∅ at hU
        rw [givenC_tsubst] at hU
        simp [givenC] at hU

/-- However, in the declarative system of Figure 6, `bad` with `π = ω` *is* typable, using the
local assumptions of rule `E_Let`: `arr` is given the qualified type `𝓛 ⇒ MArray`, so each use
of `arr` re-evaluates `new 5` with its own copy of `𝓛` (obtained by duplication), and no array is
shared.  The paper's claim that `bad` is rejected is thus a claim about the inference algorithm
(whose rule `G_Let` does not generalise constraints), which `bad_not_inferred` proves. -/
theorem bad_omega_typed : ∃ u : Fin 1 → Usage,
    Nonempty (HasType linD lnSig givenC lnΓ u (bad .omega) (pairTy arrTy arrTy)) := by
  have hL := linD_lawful 0
  let Γ₂ : Fin 2 → Scheme Unit 0 := Fin.cons ⟨0, givenC, arrTy⟩ lnΓ
  have body := pair_typed (varArr_typed (Γ := Γ₂) (x := 0) rfl)
    (varArr_typed (Γ := Γ₂) (x := 0) rfl)
  have hb : (single 0 + single 0 : Fin 2 → Usage) = Fin.cons (Usage.ofMult .omega) 0 := by
    funext i; fin_cases i <;> rfl
  have e₁ : HasType linD lnSig (0 + givenC) lnΓ (single 0) (.app (.var 0) lit) arrTy :=
    .sub (newApp_typed (Γ := lnΓ) (x := 0) rfl) (hL.entails_of_eq (zero_add _))
  have outer := HasType.let_ (Q₁ := 0) (Q := givenC) (π := .omega) e₁ (castU hb body)
  refine ⟨_, ⟨.sub outer ?_⟩⟩
  exact hL.trans (hL.dup_dup (fun _ _ => Set.mem_univ _)) (hL.entails_of_eq (by simp))

-- [PAPER ◀ END] §3.2, `bad`, `badToo` and two arrays

end Examples

end LQT
