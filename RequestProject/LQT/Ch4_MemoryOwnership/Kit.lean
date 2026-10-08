module

public import RequestProject.LQT.Ch4_MemoryOwnership.Setting

/-!
# Tools for the memory-ownership examples

Paper location: none.  Helpers to write the example programs of §1, §3.2, §4 and §6.3.2 in the
formal language, and to check them with the inference algorithm of §6:

* term-level helpers: integer literals, pairs, `Ur`, and `case` on `()`, `Ur`, pairs and `Bool`;
* the corresponding constraint-generation rules (`Gen.caseUnit'`, …);
* the simplification set `ty_norm` that computes type schemes in a context and substitutions;
* rules for the solver of Figure 9 / 10b whose outputs are computed (`Solve.oneL'`, …).
-/

@[expose] public section

noncomputable section

namespace LQT

namespace Mem

open SConstr

-- [NOT IN PAPER ▶ START] tools for the memory examples (whole file)

/-! ### Terms -/

/-- An integer literal. -/
def lit {k n : Nat} : Tm memSig k n := .con 0 ⟨0, by decide⟩

/-- The unit value `()`. -/
def unitE {k n : Nat} : Tm memSig k n := .con 1 ⟨0, by decide⟩

/-- `True`. -/
def trueE {k n : Nat} : Tm memSig k n := .con 4 ⟨0, by decide⟩

/-- The pair `(a, b)`. -/
def pairE {k n : Nat} (a b : Tm memSig k n) : Tm memSig k n :=
  .app (.app (.con 2 ⟨0, by decide⟩) a) b

/-- `Ur e`. -/
def urE {k n : Nat} (e : Tm memSig k n) : Tm memSig k n := .app (.con 3 ⟨0, by decide⟩) e

/-- `case_π e of { () → b }`. -/
def caseUnit {k n : Nat} (π : Mult) (e : Tm memSig k n) (b : Tm memSig k (0 + n)) :
    Tm memSig k n :=
  .case π e 1 (fun _ => b)

/-- `case_π e of { Ur x → b }` (`x` is the variable `0` of `b`). -/
def caseUr {k n : Nat} (π : Mult) (e : Tm memSig k n) (b : Tm memSig k (1 + n)) :
    Tm memSig k n :=
  .case π e 3 (fun _ => b)

/-- `case_π e of { (x, y) → b }` (`x` is the variable `0` and `y` the variable `1` of `b`). -/
def casePair {k n : Nat} (π : Mult) (e : Tm memSig k n) (b : Tm memSig k (2 + n)) :
    Tm memSig k n :=
  .case π e 2 (fun _ => b)

/-- `case_π e of { True → bt; False → bf }`. -/
def caseBool {k n : Nat} (π : Mult) (e : Tm memSig k n) (bt bf : Tm memSig k (0 + n)) :
    Tm memSig k n :=
  .case π e 4 (fun i => if i.val = 0 then bt else bf)

/-! ### Normalisation of types -/

theorem cons_eq_vecCons {α : Type} {m : Nat} (a : α) (f : Fin m → α) :
    (Fin.cons a f : Fin (m + 1) → α) = Matrix.vecCons a f := rfl

theorem exq_congr {P : Type} {k j m m' : Nat} {τ : Ty P (k + j)} (hm : m = m')
    {mul : Fin m → Mult} {mul' : Fin m' → Mult} {pred : Fin m → P} {pred' : Fin m' → P}
    {ar : Fin m → Nat} {ar' : Fin m' → Nat}
    {args : (i : Fin m) → Fin (ar i) → Ty P (k + j)}
    {args' : (i : Fin m') → Fin (ar' i) → Ty P (k + j)}
    (h1 : ∀ i, mul i = mul' (Fin.cast hm i)) (h2 : ∀ i, pred i = pred' (Fin.cast hm i))
    (h3 : ∀ i, ar i = ar' (Fin.cast hm i))
    (h4 : ∀ i l, args i l = args' (Fin.cast hm i) (Fin.cast (h3 i) l)) :
    (Ty.exq j τ m mul pred ar args : Ty P k) = Ty.exq j τ m' mul' pred' ar' args' := by
  subst hm
  have e1 : mul = mul' := funext h1
  have e2 : pred = pred' := funext h2
  have e3 : ar = ar' := funext h3
  subst e1 e2 e3
  have e4 : args = args' := funext fun i => funext fun l => h4 i l
  subst e4; rfl

/-- Applying a function to the types of a scaled atom description. -/
def mapC {k k' : Nat} (f : Ty Pred k → Ty Pred k') (c : Mult × Pred × List (Ty Pred k)) :
    Mult × Pred × List (Ty Pred k') := (c.1, c.2.1, c.2.2.map f)

theorem exT_subst {k k' j : Nat} (σ : Fin k → Ty Pred k') (τ : Ty Pred (k + j))
    (cs : List (Mult × Pred × List (Ty Pred (k + j)))) :
    (exT j τ cs).subst σ =
      exT j (τ.subst (liftSub j σ)) (cs.map (mapC (Ty.subst (liftSub j σ)))) := by
  simp only [exT, Ty.subst]
  refine exq_congr (by simp) (fun i => ?_) (fun i => ?_) (fun i => ?_) (fun i l => ?_) <;>
    simp [mapC]

theorem exT_rename {k k' j : Nat} (r : Fin k → Fin k') (τ : Ty Pred (k + j))
    (cs : List (Mult × Pred × List (Ty Pred (k + j)))) :
    (exT j τ cs).rename r =
      exT j (τ.rename (liftRen j r)) (cs.map (mapC (Ty.rename (liftRen j r)))) := by
  simp only [exT, Ty.rename]
  refine exq_congr (by simp) (fun i => ?_) (fun i => ?_) (fun i => ?_) (fun i l => ?_) <;>
    simp [mapC]

theorem subst_tvar {k k' : Nat} (σ : Fin k → Ty Pred k') (a : Fin k) :
    (Ty.tvar a).subst σ = σ a := rfl

theorem subst_arr {k k' : Nat} (σ : Fin k → Ty Pred k') (π : Mult) (a b : Ty Pred k) :
    (Ty.arr π a b).subst σ = Ty.arr π (a.subst σ) (b.subst σ) := rfl

theorem rename_tvar {k k' : Nat} (r : Fin k → Fin k') (a : Fin k) :
    (Ty.tvar a : Ty Pred k).rename r = Ty.tvar (r a) := rfl

theorem rename_arr {k k' : Nat} (r : Fin k → Fin k') (π : Mult) (a b : Ty Pred k) :
    (Ty.arr π a b).rename r = Ty.arr π (a.rename r) (b.rename r) := rfl

theorem subst_data {k k' : Nat} (σ : Fin k → Ty Pred k') (T p : Nat) (args : Fin p → Ty Pred k) :
    (Ty.data T p args).subst σ = Ty.data T p (Ty.subst σ ∘ args) := rfl

theorem rename_data {k k' : Nat} (r : Fin k → Fin k') (T p : Nat) (args : Fin p → Ty Pred k) :
    (Ty.data T p args).rename r = Ty.data T p (Ty.rename r ∘ args) := rfl

theorem comp_vecCons {α β : Type} {m : Nat} (f : α → β) (a : α) (v : Fin m → α) :
    f ∘ Matrix.vecCons a v = Matrix.vecCons (f a) (f ∘ v) := by
  funext i; refine Fin.cases ?_ (fun j => ?_) i <;> simp

theorem comp_vecEmpty {α β : Type} (f : α → β) : f ∘ (![] : Fin 0 → α) = ![] :=
  funext (fun i => i.elim0)

/-- The constraint of an existential type written with `exT`. -/
theorem exqC_exT {k : Nat} (cs : List (Mult × Pred × List (Ty Pred k))) :
    exqC cs.length (fun i => (cs.get i).1) (fun i => (cs.get i).2.1)
      (fun i => (cs.get i).2.2.length) (fun i l => (cs.get i).2.2.get l) =
      (cs.map (fun c => (atom c.1 ((c.2.1, c.2.2) : Atom Pred k) : SConstr (Atom Pred k)))).sum := by
  simp only [exqC]
  induction cs with
  | nil => simp
  | cons c cs ih =>
    erw [Fin.sum_univ_succ]
    simp only [List.map_cons, List.sum_cons]
    congr 1
    simp

/-- Computes the types of the variables of a context, substitutions and renamings. -/
macro "ty_norm" : tactic => `(tactic| simp [-Matrix.cons_val_fin_one, cons_eq_vecCons, ctxWk, memΓ,
  linearlyS, newS, writeS, readS, freeS, newRefS, readRefS, writeRefS, freeRefS, lengthS, splitS,
  joinS, lendMutS, unlendMutS, binopS, swapS, sortS, partitionS, goS, Scheme.rename, Scheme.mono,
  subst_tvar, subst_arr, rename_tvar, rename_arr, Ty.wk, intT, unitT, pairT, urT, boolT, uarrT, refT, marrT, rwL, evidT,
  liftRen, liftSub, instSub, Fin.addCases, caseCtx, Fin.append, exT_subst, exT_rename, mapC,
  subst_data, rename_data, comp_vecCons, comp_vecEmpty, rwQ, rdA, wrA, linA, slicesA, lentA,
  SConstr.tsubst, SConstr.rename, Atom.subst, Atom.rename, DataSig.conTy, memSig, arrows, field,
  arity, params, Fin.subNat, Fin.castPred, Fin.castLT])

/-- Proves `τ = τ'` where `τ` is computed by `ty_norm` and `τ'` may contain metavariables, which
are instantiated with the computed type. -/
macro "ty_fix" : tactic => `(tactic| ((conv_lhs => simp [-Matrix.cons_val_fin_one, cons_eq_vecCons, ctxWk, memΓ,
  linearlyS, newS, writeS, readS, freeS, newRefS, readRefS, writeRefS, freeRefS, lengthS, splitS,
  joinS, lendMutS, unlendMutS, binopS, swapS, sortS, partitionS, goS, Scheme.rename, Scheme.mono,
  subst_tvar, subst_arr, rename_tvar, rename_arr, Ty.wk, intT, unitT, pairT, urT, boolT, uarrT, refT, marrT, rwL, evidT,
  liftRen, liftSub, instSub, Fin.addCases, caseCtx, Fin.append, exT_subst, exT_rename, mapC,
  subst_data, rename_data, comp_vecCons, comp_vecEmpty, rwQ, rdA, wrA, linA, slicesA, lentA,
  SConstr.tsubst, SConstr.rename, Atom.subst, Atom.rename, DataSig.conTy, memSig, arrows, field,
  arity, params, Fin.subNat, Fin.castPred, Fin.castLT]) <;>
  (try conv_rhs => simp [-Matrix.cons_val_fin_one, cons_eq_vecCons, ctxWk, memΓ,
  linearlyS, newS, writeS, readS, freeS, newRefS, readRefS, writeRefS, freeRefS, lengthS, splitS,
  joinS, lendMutS, unlendMutS, binopS, swapS, sortS, partitionS, goS, Scheme.rename, Scheme.mono,
  subst_tvar, subst_arr, rename_tvar, rename_arr, Ty.wk, intT, unitT, pairT, urT, boolT, uarrT, refT, marrT, rwL, evidT,
  liftRen, liftSub, instSub, Fin.addCases, caseCtx, Fin.append, exT_subst, exT_rename, mapC,
  subst_data, rename_data, comp_vecCons, comp_vecEmpty, rwQ, rdA, wrA, linA, slicesA, lentA,
  SConstr.tsubst, SConstr.rename, Atom.subst, Atom.rename, DataSig.conTy, memSig, arrows, field,
  arity, params, Fin.subNat, Fin.castPred, Fin.castLT]) <;> rfl))

/-! ### Constraint generation for the helpers -/

variable {k n : Nat} {Γ : Fin n → Scheme Pred k}

theorem Gen.lit' : Gen memSig Γ 0 lit intT (.simple 0) :=
  Gen.con' 0 _ Fin.elim0 rfl

theorem Gen.unit' : Gen memSig Γ 0 unitE unitT (.simple 0) :=
  Gen.con' 1 _ Fin.elim0 rfl

theorem Gen.pair' {u₁ u₂ : Fin n → Usage} {a b : Tm memSig k n} {τa τb : Ty Pred k}
    {C₁ C₂ : Wanted (Atom Pred) k} (g₁ : Gen memSig Γ u₁ a τa C₁)
    (g₂ : Gen memSig Γ u₂ b τb C₂) :
    Gen memSig Γ (0 + (Mult.one : Mult) • u₁ + (Mult.one : Mult) • u₂) (pairE a b) (pairT τa τb)
      (.tensor (.tensor (.simple 0) ((Mult.one : Mult) • C₁)) ((Mult.one : Mult) • C₂)) :=
  Gen.app (Gen.app (Gen.con' 2 _ ![τa, τb] rfl) g₁) g₂

theorem Gen.ur' {u : Fin n → Usage} {e : Tm memSig k n} {τ : Ty Pred k}
    {C : Wanted (Atom Pred) k} (g : Gen memSig Γ u e τ C) :
    Gen memSig Γ (0 + (Mult.omega : Mult) • u) (urE e) (urT τ)
      (.tensor (.simple 0) ((Mult.omega : Mult) • C)) :=
  Gen.app (Gen.con' 3 _ ![τ] rfl) g

theorem Gen.caseUnit' {u₁ : Fin n → Usage} {U : Fin (0 + n) → Usage} {π : Mult}
    {τ : Ty Pred k} {e : Tm memSig k n} {b : Tm memSig k (0 + n)}
    {C C' : Wanted (Atom Pred) k}
    (g : Gen memSig Γ u₁ e unitT C)
    (gb : Gen memSig (caseCtx memSig Γ 1 ⟨0, by decide⟩ Fin.elim0) U b τ C')
    (h : UsageLE U (caseUsage memSig π (caseJoin (sig := memSig) 1 (fun _ => U)) 1
      ⟨0, by decide⟩)) :
    Gen memSig Γ (π • u₁ + caseJoin (sig := memSig) 1 (fun _ => U)) (caseUnit π e b) τ
      (.tensor (π • C) C') := by
  have := Gen.case' (sig := memSig) (T := 1) (τs := Fin.elim0) (alts := fun _ => b)
    (U := fun _ => U) (Cs := fun _ => C') (π := π) g
    (fun i => by match i with | ⟨0, _⟩ => exact gb)
    (fun i => by match i with | ⟨0, _⟩ => exact h)
  exact this

theorem Gen.caseUr' {u₁ : Fin n → Usage} {U : Fin (1 + n) → Usage} {π : Mult}
    {τ τ₀ : Ty Pred k} {e : Tm memSig k n} {b : Tm memSig k (1 + n)}
    {C C' : Wanted (Atom Pred) k}
    (g : Gen memSig Γ u₁ e (urT τ₀) C)
    (gb : Gen memSig (caseCtx memSig Γ 3 ⟨0, by decide⟩ ![τ₀]) U b τ C')
    (h : UsageLE U (caseUsage memSig π (caseJoin (sig := memSig) 3 (fun _ => U)) 3
      ⟨0, by decide⟩)) :
    Gen memSig Γ (π • u₁ + caseJoin (sig := memSig) 3 (fun _ => U)) (caseUr π e b) τ
      (.tensor (π • C) C') := by
  have := Gen.case' (sig := memSig) (T := 3) (τs := ![τ₀]) (alts := fun _ => b)
    (U := fun _ => U) (Cs := fun _ => C') (π := π) g
    (fun i => by match i with | ⟨0, _⟩ => exact gb)
    (fun i => by match i with | ⟨0, _⟩ => exact h)
  exact this

theorem Gen.casePair' {u₁ : Fin n → Usage} {U : Fin (2 + n) → Usage} {π : Mult}
    {τ τa τb : Ty Pred k} {e : Tm memSig k n} {b : Tm memSig k (2 + n)}
    {C C' : Wanted (Atom Pred) k}
    (g : Gen memSig Γ u₁ e (pairT τa τb) C)
    (gb : Gen memSig (caseCtx memSig Γ 2 ⟨0, by decide⟩ ![τa, τb]) U b τ C')
    (h : UsageLE U (caseUsage memSig π (caseJoin (sig := memSig) 2 (fun _ => U)) 2
      ⟨0, by decide⟩)) :
    Gen memSig Γ (π • u₁ + caseJoin (sig := memSig) 2 (fun _ => U)) (casePair π e b) τ
      (.tensor (π • C) C') := by
  have := Gen.case' (sig := memSig) (T := 2) (τs := ![τa, τb]) (alts := fun _ => b)
    (U := fun _ => U) (Cs := fun _ => C') (π := π) g
    (fun i => by match i with | ⟨0, _⟩ => exact gb)
    (fun i => by match i with | ⟨0, _⟩ => exact h)
  exact this

/-- The usages of the two alternatives of a `case` on `Bool`. -/
def boolU (Ut Uf : Fin (0 + n) → Usage) : (i : Fin (memSig.ncons 4)) →
    Fin (memSig.arity 4 i + n) → Usage := fun i => if i.val = 0 then Ut else Uf

theorem Gen.caseBool' {u₁ : Fin n → Usage} {Ut Uf : Fin (0 + n) → Usage} {π : Mult}
    {τ : Ty Pred k} {e : Tm memSig k n} {bt bf : Tm memSig k (0 + n)}
    {C Ct Cf : Wanted (Atom Pred) k}
    (g : Gen memSig Γ u₁ e boolT C)
    (gt : Gen memSig (caseCtx memSig Γ 4 ⟨0, by decide⟩ Fin.elim0) Ut bt τ Ct)
    (gf : Gen memSig (caseCtx memSig Γ 4 ⟨1, by decide⟩ Fin.elim0) Uf bf τ Cf)
    (ht : UsageLE Ut (caseUsage memSig π (caseJoin (sig := memSig) 4 (boolU Ut Uf)) 4
      ⟨0, by decide⟩))
    (hf : UsageLE Uf (caseUsage memSig π (caseJoin (sig := memSig) 4 (boolU Ut Uf)) 4
      ⟨1, by decide⟩)) :
    Gen memSig Γ (π • u₁ + caseJoin (sig := memSig) 4 (boolU Ut Uf)) (caseBool π e bt bf) τ
      (.tensor (π • C) (.amp Ct Cf)) := by
  have := Gen.case' (sig := memSig) (T := 4) (τs := Fin.elim0)
    (alts := fun i => if i.val = 0 then bt else bf)
    (U := boolU Ut Uf) (Cs := ![Ct, Cf]) (π := π) g
    (fun i => by
      match i with
      | ⟨0, _⟩ => exact gt
      | ⟨1, _⟩ => exact gf)
    (fun i => by
      match i with
      | ⟨0, _⟩ => exact ht
      | ⟨1, _⟩ => exact hf)
  exact this

/-! ### Solving -/

/-- The tensor product of a list of scaled atoms. -/
def atomsOf {k : Nat} (l : List (Mult × Atom Pred k)) : SConstr (Atom Pred k) :=
  (l.map (fun p => atom p.1 p.2)).sum

@[simp] theorem atomsOf_nil {k : Nat} : atomsOf ([] : List (Mult × Atom Pred k)) = 0 := rfl

theorem atomsOf_cons_eq {k : Nat} (p : Mult × Atom Pred k) (l : List (Mult × Atom Pred k)) :
    atomsOf (p :: l) = atom p.1 p.2 + atomsOf l := by
  simp [atomsOf]

theorem exqC_eq_atomsOf {k m : Nat} (mul : Fin m → Mult) (pred : Fin m → Pred) (ar : Fin m → Nat)
    (args : (i : Fin m) → Fin (ar i) → Ty Pred k) :
    exqC m mul pred ar args =
      atomsOf (List.ofFn fun i => (mul i, ((pred i, List.ofFn (args i)) : Atom Pred k))) := by
  simp only [exqC, atomsOf, List.map_ofFn, List.sum_ofFn]
  rfl

theorem map_atomsOf {k k' : Nat} (f : Atom Pred k → Atom Pred k') (l : List (Mult × Atom Pred k)) :
    (atomsOf l).map f = atomsOf (l.map fun p => (p.1, f p.2)) := by
  induction l with
  | nil => simp
  | cons p l ih => simp [atomsOf_cons_eq, ih]

theorem atomsOf_U_cons {k : Nat} (p : Mult × Atom Pred k) (l : List (Mult × Atom Pred k)) :
    (atomsOf (p :: l)).U = (atom p.1 p.2).U ∪ (atomsOf l).U := by
  simp [atomsOf_cons_eq]

theorem memD_dup {k : Nat} : (memD k).Dup = {q | q.1 = Pred.lin} := rfl

theorem atom_mk_eq {k : Nat} (p p' : Pred) (l l' : List (Ty Pred k)) :
    (@Eq (Atom Pred k) (p, l) (p', l')) = (p = p' ∧ l = l') := Prod.mk.injEq _ _ _ _

/-- The linear atoms of a list of scaled atoms. -/
def linAtoms {k : Nat} (l : List (Mult × Atom Pred k)) : List (Atom Pred k) :=
  (l.filter (fun p => p.1 == .one)).map Prod.snd

@[simp] theorem linAtoms_nil {k : Nat} : linAtoms ([] : List (Mult × Atom Pred k)) = [] := rfl
@[simp] theorem linAtoms_cons_one {k : Nat} (q : Atom Pred k) (l : List (Mult × Atom Pred k)) :
    linAtoms ((.one, q) :: l) = q :: linAtoms l := by simp [linAtoms]
@[simp] theorem linAtoms_cons_omega {k : Nat} (q : Atom Pred k) (l : List (Mult × Atom Pred k)) :
    linAtoms ((.omega, q) :: l) = linAtoms l := by simp [linAtoms]

theorem linAtoms_L {k : Nat} (l : List (Mult × Atom Pred k)) :
    ((linAtoms l : List (Atom Pred k)) : Multiset (Atom Pred k)) = (atomsOf l).L := by
  induction l with
  | nil => rfl
  | cons p l ih =>
    obtain ⟨π, q⟩ := p
    cases π <;> simp [atomsOf_cons_eq, ← ih, atom, Multiset.singleton_add]

variable {U : Finset (Atom Pred k)} {Dl : List (Atom Pred k)}

theorem simpleSolver_of_simpleSolve {A : Type*} [DecidableEq A] (l : A) {U : Finset A}
    {Dl Li : List A} {π : Mult} {q : A} {Lo : List A} (h : simpleSolve l U Dl Li π q = some Lo) :
    simpleSolver l U Dl Li π q Lo := by
  cases π with
  | omega =>
    simp only [simpleSolve] at h
    split_ifs at h with hq
    cases h
    exact .many hq
  | one =>
    simp only [simpleSolve] at h
    split_ifs at h with hU hDL hLi hl'
    · cases h
      exact .oneU hU (by simpa [not_or] using hDL)
    · cases h
      obtain ⟨L₁, L₂, rfl, h₂⟩ := exists_split_last hLi
      rw [eraseLast_append_cons _ _ h₂]
      exact .oneL L₁ L₂ h₂ hU
    · cases h
      obtain ⟨rfl, hlast⟩ := hl'
      obtain ⟨Dl', rfl⟩ : ∃ Dl', Dl = Dl' ++ [q] := by
        rw [List.getLast?_eq_some_iff] at hlast
        exact hlast
      exact .oneD hU

/-- An atom, solved by the (functional form of the) atomic solver of Figure 10b. -/
theorem Solve.atom' {Li Lo : List (Atom Pred k)} {π : Mult} {q : Atom Pred k}
    (h : simpleSolve linA U Dl Li π q = some Lo) :
    Solve memD memS U Dl Li (.simple (atom π q)) Lo :=
  .atom (simpleSolver_of_simpleSolve _ h)

theorem Solve.atomsOf_nil {Li : List (Atom Pred k)} :
    Solve memD memS U Dl Li (.simple (atomsOf [])) Li := .empty

theorem Solve.atomsOf_cons {Li Lo' Lo : List (Atom Pred k)} {p : Mult × Atom Pred k}
    {l : List (Mult × Atom Pred k)}
    (h₁ : Solve memD memS U Dl Li (.simple (atom p.1 p.2)) Lo')
    (h₂ : Solve memD memS U Dl Lo' (.simple (atomsOf l)) Lo) :
    Solve memD memS U Dl Li (.simple (atomsOf (p :: l))) Lo := by
  rw [atomsOf_cons_eq]; exact .split h₁ h₂

open Classical in
/-- Rule S_ImplOne for an assumption given as a list of scaled atoms. -/
theorem Solve.implOne_atoms {j : Nat} {Li Lo : List (Atom Pred k)}
    (l : List (Mult × Atom Pred (k + j))) {C : Wanted (Atom Pred) (k + j)}
    (h : Solve memD memS (U.image (Weakening.wk j) ∪ (atomsOf l).U)
        ((linAtoms l).filter (fun x => decide (x ∈ (memD (k + j)).Dup)) ++
          Dl.map (Weakening.wk j))
        (Li.map (Weakening.wk j) ++ (linAtoms l).filter (fun x => decide (x ∉ (memD (k + j)).Dup)))
        C (Lo.map (Weakening.wk j)))
    (hle : (Lo : Multiset (Atom Pred k)) ≤ Li) :
    Solve memD memS U Dl Li (.impl .one j (atomsOf l) C) Lo :=
  .implOne (linAtoms l) (linAtoms_L l) h hle

open Classical in
/-- Rule S_ImplMany for an assumption given as a list of scaled atoms. -/
theorem Solve.implMany_atoms {j : Nat} {Li : List (Atom Pred k)}
    (l : List (Mult × Atom Pred (k + j))) {C : Wanted (Atom Pred) (k + j)}
    (h : Solve memD memS (U.image (Weakening.wk j) ∪ (atomsOf l).U)
        ((linAtoms l).filter (fun x => decide (x ∈ (memD (k + j)).Dup)))
        ((linAtoms l).filter (fun x => decide (x ∉ (memD (k + j)).Dup))) C []) :
    Solve memD memS U Dl Li (.impl .omega j (atomsOf l) C) Li :=
  .implMany (linAtoms l) (linAtoms_L l) h

/-- An implication whose assumption is the tensor product of two scaled atoms. -/
theorem Solve.impl_add {j : Nat} {π : Mult} {Li Lo : List (Atom Pred k)} {π₁ π₂ : Mult}
    {a b : Atom Pred (k + j)} {C : Wanted (Atom Pred) (k + j)}
    (h : Solve memD memS U Dl Li (.impl π j (atomsOf [(π₁, a), (π₂, b)]) C) Lo) :
    Solve memD memS U Dl Li (.impl π j (atom π₁ a + atom π₂ b) C) Lo := by
  simpa [atomsOf_cons_eq] using h

/-- Normalises a goal of the solver: computes the wanted constraint and the contexts. -/
macro "w_norm" : tactic => `(tactic| simp [-Matrix.cons_val_fin_one, cons_eq_vecCons, ctxWk, memΓ,
  linearlyS, newS, writeS, readS, freeS, newRefS, readRefS, writeRefS, freeRefS, lengthS, splitS,
  joinS, lendMutS, unlendMutS, binopS, swapS, sortS, partitionS, goS, Scheme.rename, Scheme.mono,
  subst_tvar, subst_arr, rename_tvar, rename_arr, Ty.wk, intT, unitT, pairT, urT, boolT, uarrT, refT, marrT, rwL, evidT,
  liftRen, liftSub, instSub, Fin.addCases, caseCtx, Fin.append, exT_subst, exT_rename, mapC,
  subst_data, rename_data, comp_vecCons, comp_vecEmpty, rwQ, rdA, wrA, linA, slicesA, lentA,
  SConstr.tsubst, SConstr.rename, Atom.subst, Atom.rename, DataSig.conTy, memSig, arrows, field,
  arity, params, Fin.subNat, Fin.castPred, Fin.castLT, exqC_eq_atomsOf, map_atomsOf,
  List.ofFn_succ, List.ofFn_zero, List.map_cons, List.map_nil, wk_atom_def, SConstr.wk,
  Wanted.one_smul, Wanted.smul_simple, Wanted.smul_tensor, Wanted.smul_impl, Wanted.omega_smul_amp,
  Wanted.one_smul_amp, SConstr.one_smul', smul_atom, atomsOf_nil, linAtoms, linAtoms_cons_one,
  linAtoms_cons_omega, linAtoms_nil, List.filter_cons, List.filter_nil, List.nil_append,
  List.cons_append, List.append_nil, Finset.image_empty, Finset.empty_union, Finset.union_empty,
  SConstr.add_U, SConstr.zero_U, SConstr.atom_one_U, SConstr.atom_omega_U,
  memD_dup, atomsOf_U_cons, atom_mk_eq, Function.comp_apply, Atom.rename, Set.mem_setOf_eq, Set.mem_singleton_iff, decide_true,
  decide_false, decide_not, Bool.not_true, Bool.not_false, ite_true, ite_false, cond_true,
  cond_false, SConstr.map_zero, SConstr.map_add, SConstr.map_atom])

/-- Evaluates the atomic solver on a goal `simpleSolve … = some ?Lo`. -/
macro "atom_eval" : tactic => `(tactic| ((conv_lhs => simp [simpleSolve, eraseLast, linA, rdA, wrA,
  lentA, slicesA, List.erase_cons, beq_iff_eq, atom_mk_eq, Function.comp_apply, wk_atom_def,
  Atom.rename, rename_tvar, List.map_cons, List.map_nil, List.reverse_cons, List.reverse_nil]) <;> rfl))

/-- Runs the solver of Figure 9 on a normalised goal. -/
macro "solve_auto" : tactic => `(tactic| repeat (first
  | exact Solve.empty
  | exact Solve.atomsOf_nil
  | (apply Solve.mult)
  | (apply Solve.add)
  | (apply Solve.atomsOf_cons)
  | (apply Solve.split)
  | (apply Solve.atom'; atom_eval)
  | (apply Solve.implOne_atoms; w_norm)
  | (apply Solve.impl_add)
  | (apply Solve.implMany_atoms; w_norm)
  | (exact Multiset.zero_le _)))

-- [NOT IN PAPER ◀ END] tools for the memory examples

end Mem

end LQT
