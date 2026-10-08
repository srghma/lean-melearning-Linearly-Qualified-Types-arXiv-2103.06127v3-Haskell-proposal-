module

public import RequestProject.LQT.Ch6_ConstraintInference.GenKit
public import RequestProject.LQT.Ch6_ConstraintInference.FreeLDomain
public import RequestProject.LQT.Ch6_ConstraintInference.AtomicSolverProps

/-!
# The setting of the memory-ownership examples (§1, §3.2, §4, Figures 1–3)

Paper location: §1 "Introduction" (`read2AndDiscard`), §3 Figure 1 "Interfaces for mutable
arrays", §3.2 (the `linearly` primitive), §4 "Application: memory ownership" (§4.1 capability
constraints and atomic references, §4.2 arrays, borrowing and slices) and Figures 2–3.  The
start and end of each part is marked by `-- [PAPER ▶ START]` / `-- [PAPER ◀ END]` comments.

We write the APIs of the paper in the formal language of §5 (de Bruijn indices for type and
expression variables):

* **Atomic constraints** are predicate symbols applied to types: `Linearly` (`𝓛`, no argument),
  `Read n`, `Write n`, `Slices n l r`, and `Lent n p` (used by our encoding of borrowing, see
  below).  The constraint domain is the stripped-down domain of Figure 10a, in which exactly the
  atom `Linearly` is duplicable (`memD`), and inference uses the atomic solver of Figure 10b.
* **Data types** (`memSig`): `Int` (one nullary constructor standing for every integer
  literal), `()`, linear pairs `(a, b)`, `Ur a` (one unrestricted field), `Bool`, and the
  abstract types `UArray a n`, `AtomRef a n` and `MArray a` (no constructors).
* **The APIs** are the type schemes of the variables of the context `memΓ` (top-level
  definitions are unrestricted, so the examples may use them any number of times).  A return
  type `τ ⧀ Q` is the existential type `∃. τ ⇐ Q` with no type variable.

Three features of the paper's Haskell code are outside the formal language; we encode them:

* **Qualified argument types** (`linearly :: (Linearly =⚬ Ur r) ⊸ Ur r`).  An argument of type
  `Q =⚬ τ` is passed as a linear function from *evidence* for `Q`, the value type
  `Evid Q = ∃. () ⇐ Q`: the continuation unpacks its argument (`let pack _ = ev in …`) to bring
  `Q` into scope.  This is the dictionary-passing reading of `Q =⚬ τ`, which is also how §7
  desugars it (to a linear function taking the evidence of `Q`).
* **Rank-2 continuations** (`lendMut :: … -> (∀ p. RW p =⚬ a p -> r ⧀ RW p) ⊸ r ⧀ RW n`).
  We use the equivalent direct style: `lendMut` returns (unrestricted, like the argument of the
  continuation) a reference at a fresh location `p` with the capabilities `RW p` and a token
  `Lent n p`, and `unlendMut` consumes `RW p` and `Lent n p` to give back `RW n`.  As in the paper, `RW n` and `RW p` are never simultaneously available.
* **Recursion and higher-kinded type parameters.**  The language has no recursive definitions:
  a recursive definition with a signature is checked against its signature, which is in the
  context (as GHC does).  The local function `go` of Figure 3 is lambda-lifted.  `PArray a n`
  with `a :: Location -> Type` is specialised to `UArray a n` (arrays of `AtomRef a`).
-/

@[expose] public section

noncomputable section

namespace LQT

namespace Mem

open SConstr

-- [PAPER ▶ START] §4.1 "Capability constraints", §3.2 (`Linearly`): the atomic constraints

/-- Predicate symbols of the atomic constraints. -/
inductive Pred
  /-- `Linearly` (written `𝓛` in Figure 10). -/
  | lin
  /-- `Read n`. -/
  | rd
  /-- `Write n`. -/
  | wr
  /-- `Slices n l r`. -/
  | slices
  /-- `Lent n p` (our direct-style encoding of `lendMut`). -/
  | lent
  deriving DecidableEq

/-- `Linearly`. -/
def linA {k : Nat} : Atom Pred k := (.lin, [])
/-- `Read n`. -/
def rdA {k : Nat} (n : Ty Pred k) : Atom Pred k := (.rd, [n])
/-- `Write n`. -/
def wrA {k : Nat} (n : Ty Pred k) : Atom Pred k := (.wr, [n])
/-- `Slices n l r`. -/
def slicesA {k : Nat} (n l r : Ty Pred k) : Atom Pred k := (.slices, [n, l, r])
/-- `Lent n p`. -/
def lentA {k : Nat} (n p : Ty Pred k) : Atom Pred k := (.lent, [n, p])

/-- `RW n = (Read n, Write n)`, as a (linear) simple constraint. -/
def rwQ {k : Nat} (n : Ty Pred k) : SConstr (Atom Pred k) := atom .one (rdA n) + atom .one (wrA n)

/-- The constraint domain: Figure 10a, with `Linearly` the only duplicable atom. -/
def memD : LDomain (Atom Pred) := predLDomain {Pred.lin}

/-- The atomic solver of Figure 10b, at every level. -/
def memS : (k : Nat) → AtomSolver (Atom Pred k) := fun _ => simpleSolver linA

-- [PAPER ◀ END] the atomic constraints

-- [PAPER ▶ START] §4, Figure 1: the data types

/-- Number of type parameters: pairs (`2`), `Ur` (`3`), `UArray` (`5`), `AtomRef` (`6`),
`MArray` (`7`). -/
def params : Nat → Nat
  | 2 => 2
  | 3 => 1
  | 5 => 2
  | 6 => 2
  | 7 => 1
  | _ => 0

/-- Number of constructors: `Int` (`0`), `()` (`1`), pairs (`2`), `Ur` (`3`), `Bool` (`4`);
the array and reference types are abstract. -/
def ncons : Nat → Nat
  | 0 => 1
  | 1 => 1
  | 2 => 1
  | 3 => 1
  | 4 => 2
  | _ => 0

/-- Number of fields of the constructors. -/
def arity : (T : Nat) → Fin (ncons T) → Nat
  | 2, _ => 2
  | 3, _ => 1
  | _, _ => 0

/-- Fields: pairs have two linear fields, `Ur` one unrestricted field. -/
def field : (T : Nat) → (i : Fin (ncons T)) → Fin (arity T i) → Mult × Ty Pred (params T)
  | 0, _, l => l.elim0
  | 1, _, l => l.elim0
  | 2, _, l => (.one, .tvar l)
  | 3, _, _ => (.omega, .tvar (⟨0, by decide⟩ : Fin 1))
  | 4, _, l => l.elim0
  | _ + 5, i, _ => i.elim0

/-- The data type signature of the memory examples. -/
def memSig : DataSig Pred := ⟨params, ncons, arity, field⟩

/-- `Int`. -/
def intT {k : Nat} : Ty Pred k := .data 0 0 ![]
/-- `()`. -/
def unitT {k : Nat} : Ty Pred k := .data 1 0 ![]
/-- `(a, b)` (linear pairs). -/
def pairT {k : Nat} (a b : Ty Pred k) : Ty Pred k := .data 2 2 ![a, b]
/-- `Ur a`. -/
def urT {k : Nat} (a : Ty Pred k) : Ty Pred k := .data 3 1 ![a]
/-- `Bool`. -/
def boolT {k : Nat} : Ty Pred k := .data 4 0 ![]
/-- `UArray a n`. -/
def uarrT {k : Nat} (a n : Ty Pred k) : Ty Pred k := .data 5 2 ![a, n]
/-- `AtomRef a n`. -/
def refT {k : Nat} (a n : Ty Pred k) : Ty Pred k := .data 6 2 ![a, n]
/-- `MArray a` (Figure 1a). -/
def marrT {k : Nat} (a : Ty Pred k) : Ty Pred k := .data 7 1 ![a]

/-- The existential type `∃ā. τ ⇐ Q` where `ā` has `j` variables and `Q` is the tensor product
of the listed scaled atoms. -/
def exT {k : Nat} (j : Nat) (τ : Ty Pred (k + j)) (cs : List (Mult × Pred × List (Ty Pred (k + j)))) :
    Ty Pred k :=
  .exq j τ cs.length (fun i => (cs.get i).1) (fun i => (cs.get i).2.1)
    (fun i => (cs.get i).2.2.length) (fun i l => (cs.get i).2.2.get l)

/-- The scaled atoms of `RW n`. -/
def rwL {k : Nat} (n : Ty Pred k) : List (Mult × Pred × List (Ty Pred k)) :=
  [(.one, .rd, [n]), (.one, .wr, [n])]

/-- Evidence for a constraint, as a value: `Evid Q = ∃. () ⇐ Q`.  A qualified argument type
`Q =⚬ τ` is encoded as `Evid Q ⊸ τ`. -/
def evidT {k : Nat} (cs : List (Mult × Pred × List (Ty Pred (k + 0)))) : Ty Pred k :=
  exT 0 unitT cs

-- [PAPER ◀ END] the data types

-- [PAPER ▶ START] §3.2 `linearly`, Figure 1b (array API with linear constraints), §4.1 (atomic
--   references), §4.2 (arrays, borrowing, slices), Figures 2–3 (signatures of `swap`, `sort`,
--   `partition` and the lifted `go`)

/-- `linearly :: (Linearly =⚬ Ur r) ⊸ Ur r`, i.e. `∀r. (Evid Linearly ⊸ Ur r) ⊸ Ur r`. -/
def linearlyS : Scheme Pred 0 :=
  ⟨1, 0, .arr .one (.arr .one (evidT [(.one, .lin, [])]) (urT (.tvar 0))) (urT (.tvar 0))⟩

/-- `new :: Linearly =⚬ Int -> ∃ n. Ur (UArray a n) ⧀ RW n`.  Figure 1b writes the result type
`∃ n. UArray a n ⧀ RW n`, but the code of §6.3.2 unpacks it as `pack (Ur arr) = new 10`: the
array must be unrestricted, since the variable bound by `pack` is linear and the array is then
passed to unrestricted arguments (`free`, `read`, …).  We follow the code. -/
def newS : Scheme Pred 0 :=
  ⟨1, atom .one linA, .arr .omega intT (exT 1 (urT (uarrT (.tvar 0) (.tvar 1))) (rwL (.tvar 1)))⟩

/-- `write :: RW n =⚬ UArray a n -> Int -> a -> () ⧀ RW n` (Figure 1b). -/
def writeS : Scheme Pred 0 :=
  ⟨2, rwQ (.tvar 1), .arr .omega (uarrT (.tvar 0) (.tvar 1)) (.arr .omega intT
    (.arr .omega (.tvar 0) (exT 0 unitT (rwL (.tvar 1)))))⟩

/-- `read :: Read n =⚬ UArray a n -> Int -> Ur a ⧀ Read n` (Figure 1b). -/
def readS : Scheme Pred 0 :=
  ⟨2, atom .one (rdA (.tvar 1)), .arr .omega (uarrT (.tvar 0) (.tvar 1)) (.arr .omega intT
    (exT 0 (urT (.tvar 0)) [(.one, .rd, [.tvar 1])]))⟩

/-- `free :: RW n =⚬ UArray a n -> ()` (Figure 1b). -/
def freeS : Scheme Pred 0 :=
  ⟨2, rwQ (.tvar 1), .arr .omega (uarrT (.tvar 0) (.tvar 1)) unitT⟩

/-- `newRef :: Linearly =⚬ ∃ n. Ur (AtomRef a n) ⧀ RW n` (§4.1, where the result is
`∃ n. AtomRef a n ⧀ RW n`; the reference is returned unrestricted for the same reason as in
`new`). -/
def newRefS : Scheme Pred 0 :=
  ⟨1, atom .one linA, exT 1 (urT (refT (.tvar 0) (.tvar 1))) (rwL (.tvar 1))⟩

/-- `readRef :: Read n =⚬ AtomRef a n -> Ur a ⧀ Read n` (§4.1). -/
def readRefS : Scheme Pred 0 :=
  ⟨2, atom .one (rdA (.tvar 1)), .arr .omega (refT (.tvar 0) (.tvar 1))
    (exT 0 (urT (.tvar 0)) [(.one, .rd, [.tvar 1])])⟩

/-- `writeRef :: RW n =⚬ AtomRef a n -> a -> () ⧀ RW n` (§4.1). -/
def writeRefS : Scheme Pred 0 :=
  ⟨2, rwQ (.tvar 1), .arr .omega (refT (.tvar 0) (.tvar 1))
    (.arr .omega (.tvar 0) (exT 0 unitT (rwL (.tvar 1))))⟩

/-- `freeRef :: RW n =⚬ AtomRef a n -> ()` (§4.1). -/
def freeRefS : Scheme Pred 0 :=
  ⟨2, rwQ (.tvar 1), .arr .omega (refT (.tvar 0) (.tvar 1)) unitT⟩

/-- `length :: PArray a n -> Int` (§4.2). -/
def lengthS : Scheme Pred 0 :=
  ⟨2, 0, .arr .omega (uarrT (.tvar 0) (.tvar 1)) intT⟩

/-- `split :: RW n =⚬ PArray a n -> Int -> ∃ l r. Ur (PArray a l, PArray a r) ⧀ (RW l, RW r,
Slices n l r)` (§4.2).  Type variables: `a = 0`, `n = 1`, and `l = 2`, `r = 3` under `∃`. -/
def splitS : Scheme Pred 0 :=
  ⟨2, rwQ (.tvar 1), .arr .omega (uarrT (.tvar 0) (.tvar 1)) (.arr .omega intT
    (exT 2 (urT (pairT (uarrT (.tvar 0) (.tvar 2)) (uarrT (.tvar 0) (.tvar 3))))
      (rwL (.tvar 2) ++ rwL (.tvar 3) ++ [(.one, .slices, [.tvar 1, .tvar 2, .tvar 3])])))⟩

/-- `join :: (Slices n l r, RW r, RW l) =⚬ PArray a l -> PArray a r -> Ur (PArray a n) ⧀ RW n`
(§4.2).  Type variables: `a = 0`, `n = 1`, `l = 2`, `r = 3`. -/
def joinS : Scheme Pred 0 :=
  ⟨4, atom .one (slicesA (.tvar 1) (.tvar 2) (.tvar 3)) + rwQ (.tvar 2) + rwQ (.tvar 3),
    .arr .omega (uarrT (.tvar 0) (.tvar 2)) (.arr .omega (uarrT (.tvar 0) (.tvar 3))
      (exT 0 (urT (uarrT (.tvar 0) (.tvar 1))) (rwL (.tvar 1))))⟩

/-- Direct-style
`lendMut :: RW n =⚬ PArray a n -> Int -> ∃ p. Ur (AtomRef a p) ⧀ (RW p, Lent n p)`
(our encoding of the rank-2 `lendMut` of §4.2.1, whose continuation receives the reference as
an unrestricted argument `a p -> …`).  Type variables: `a = 0`, `n = 1`, and `p = 2` under
`∃`. -/
def lendMutS : Scheme Pred 0 :=
  ⟨2, rwQ (.tvar 1), .arr .omega (uarrT (.tvar 0) (.tvar 1)) (.arr .omega intT
    (exT 1 (urT (refT (.tvar 0) (.tvar 2))) (rwL (.tvar 2) ++ [(.one, .lent, [.tvar 1, .tvar 2])])))⟩

/-- `unlendMut :: (RW p, Lent n p) =⚬ AtomRef a p -> () ⧀ RW n`, which ends a borrow.  Type
variables: `a = 0`, `n = 1`, `p = 2`. -/
def unlendMutS : Scheme Pred 0 :=
  ⟨3, rwQ (.tvar 2) + atom .one (lentA (.tvar 1) (.tvar 2)),
    .arr .omega (refT (.tvar 0) (.tvar 2)) (exT 0 unitT (rwL (.tvar 1)))⟩

/-- A binary operation on integers, `Int -> Int -> τ`. -/
def binopS (τ : Ty Pred 0) : Scheme Pred 0 := ⟨0, 0, .arr .omega intT (.arr .omega intT τ)⟩

/-- `swap :: RW n =⚬ PArray AtomRef n -> Int -> Int -> () ⧀ RW n` (Figure 2; the elements are
`AtomRef Int`). -/
def swapS : Scheme Pred 0 :=
  ⟨1, rwQ (.tvar 0), .arr .omega (uarrT intT (.tvar 0)) (.arr .omega intT (.arr .omega intT
    (exT 0 unitT (rwL (.tvar 0)))))⟩

/-- `sort :: RW n =⚬ UArray Int n -> () ⧀ RW n` (Figure 3). -/
def sortS : Scheme Pred 0 :=
  ⟨1, rwQ (.tvar 0), .arr .omega (uarrT intT (.tvar 0)) (exT 0 unitT (rwL (.tvar 0)))⟩

/-- `partition :: RW n =⚬ UArray Int n -> Ur Int ⧀ RW n` (Figure 3, where the result is `Int`:
see the module documentation of `QuickSort.lean` for why the index is returned in `Ur`). -/
def partitionS : Scheme Pred 0 :=
  ⟨1, rwQ (.tvar 0), .arr .omega (uarrT intT (.tvar 0)) (exT 0 (urT intT) (rwL (.tvar 0)))⟩

/-- The local `go :: RW n =⚬ Int -> Int -> Int ⧀ RW n` of Figure 3, lambda-lifted over the
variables `arr`, `last` and `pivot` it captures, and returning `Ur Int` like `partition`:
`go :: RW n =⚬ UArray Int n -> Int -> Int -> Int -> Int -> Ur Int ⧀ RW n`. -/
def goS : Scheme Pred 0 :=
  ⟨1, rwQ (.tvar 0), .arr .omega (uarrT intT (.tvar 0)) (.arr .omega intT (.arr .omega intT
    (.arr .omega intT (.arr .omega intT (exT 0 (urT intT) (rwL (.tvar 0)))))))⟩

/-- The context of the memory examples (de Bruijn indices in comments). -/
def memΓ : Fin 22 → Scheme Pred 0 :=
  ![linearlyS,    -- 0
    newS,         -- 1
    writeS,       -- 2
    readS,        -- 3
    freeS,        -- 4
    newRefS,      -- 5
    readRefS,     -- 6
    writeRefS,    -- 7
    freeRefS,     -- 8
    lengthS,      -- 9
    splitS,       -- 10
    joinS,        -- 11
    lendMutS,     -- 12
    unlendMutS,   -- 13
    binopS boolT, -- 14: `(==)`
    binopS boolT, -- 15: `(>)`
    binopS intT,  -- 16: `(+)`
    binopS intT,  -- 17: `(-)`
    swapS,        -- 18
    sortS,        -- 19
    partitionS,   -- 20
    goS]          -- 21

-- [PAPER ◀ END] the APIs

-- [NOT IN PAPER ▶ START] inference judgement for the examples, and its soundness

/-- `e` is accepted by the inference algorithm of §6 (constraint generation, Figure 8, then the
solver of Figure 9 with the atomic solver of Figure 10b), with given unrestricted constraints
`U`, duplicable linear constraints `Dl` and linear constraints `Li`. -/
def Infers {k n : Nat} (Γ : Fin n → Scheme Pred k) (U : Finset (Atom Pred k))
    (Dl Li : List (Atom Pred k)) (e : Tm memSig k n) (τ : Ty Pred k) : Prop :=
  ∃ (u : Fin n → Usage) (W : Wanted (Atom Pred) k),
    Gen memSig Γ u e τ W ∧ Solve memD memS U Dl Li W []

lemma memD_lawful : memD.Lawful := predLDomain_lawful _

/-- Programs accepted by inference are well typed (Lemmas 6.4 and 6.5). -/
theorem Infers.typed {k n : Nat} {Γ : Fin n → Scheme Pred k} {U : Finset (Atom Pred k)}
    {Dl Li : List (Atom Pred k)} {e : Tm memSig k n} {τ : Ty Pred k}
    (h : Infers Γ U Dl Li e τ) (hDl : ∀ x ∈ Dl, x = linA) :
    ∃ u, Nonempty (HasType memD memSig ⟨U, (Dl : Multiset (Atom Pred k)) + Li⟩ Γ u e τ) := by
  obtain ⟨u, W, hG, hS⟩ := h
  refine ⟨u, memD_lawful.infer_sound (fun k => simpleSolver_sound (memD_lawful.lawful k) _) hG
    ?_ hS⟩
  intro x hx
  rw [hDl x hx]
  show linA.1 ∈ ({Pred.lin} : Set Pred)
  rfl

/-- Programs accepted by inference with only linear given constraints `Li` are well typed under
`Li`. -/
theorem Infers.typed' {k n : Nat} {Γ : Fin n → Scheme Pred k} {U : Finset (Atom Pred k)}
    {Li : List (Atom Pred k)} {e : Tm memSig k n} {τ : Ty Pred k}
    (h : Infers Γ U [] Li e τ) :
    ∃ u, Nonempty (HasType memD memSig ⟨U, (Li : Multiset (Atom Pred k))⟩ Γ u e τ) := by
  simpa using h.typed (by simp)

-- [NOT IN PAPER ◀ END] inference judgement

end Mem

end LQT
