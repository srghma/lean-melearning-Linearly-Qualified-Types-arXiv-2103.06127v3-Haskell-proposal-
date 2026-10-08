module

public import RequestProject.LQT.Ch4_MemoryOwnership.Kit

/-!
# In-place quicksort (Figure 3)

Paper location: §4.2.3 "In-place quicksort", Figure 3 "In-place quicksort".

```
sort :: RW n =⚬ UArray Int n -> () ⧀ RW n
sort arr = let len = length arr in
  if len <= 1 then pack ()
  else let pack pivotIdx    = partition arr
           pack (Ur (l, r)) = split arr pivotIdx
           pack ()          = sort l
           pack ()          = sort r
           pack (Ur _)      = join l r
       in pack ()

partition :: RW n =⚬ UArray Int n -> Int ⧀ RW n
partition arr =
  let last         = length arr - 1
      pack (Ur pivot) = read arr last
      go :: RW n =⚬ Int -> Int -> Int ⧀ RW n
      go l r
        | l > r     = let pack () = swap arr last l in pack l
        | otherwise = let pack (Ur lVal) = read arr l in
                      if lVal > pivot
                      then let pack () = swap arr l r in go l (r - 1)
                      else go (l + 1) r
  in go 0 (last - 1)
```

We write the three functions in the formal language (de Bruijn indices; the APIs, `swap` and
the three functions themselves are variables of the context `memΓ`, see `Setting.lean`), with
these differences:

* **Recursion.**  Each definition is checked against its signature, which is in the context
  (`sort` calls `sort`, `go` calls `go`), as GHC does for recursive definitions with a
  signature.  The local function `go` is lambda-lifted: it takes the variables `arr`, `last`
  and `pivot` it captures as extra arguments.
* **The pivot index is returned in `Ur`** (`partition :: RW n =⚬ UArray Int n -> Ur Int ⧀ RW n`,
  and likewise for `go`).  In Figure 3, `pack pivotIdx = partition arr` binds `pivotIdx`
  *linearly* (rule E_Unpack binds the variable with multiplicity `1`), and `pivotIdx` is then
  passed to `split arr pivotIdx`, whose `Int` argument is unrestricted: this is rejected by the
  type system of §5 (as by Linear Haskell, where one would first `move` the `Int`).  Wrapping
  the index in `Ur` is the standard fix.
* `if len <= 1 then A else B` is written `if len > 1 then B else A` (the context provides `>`).

The theorems `sort_inferred`, `partition_inferred` and `go_inferred` say that each body is
accepted by the inference algorithm of §6 (constraint generation, Figure 8, then the solver of
Figures 9 and 10b) at the type of its signature with given constraint `RW n`; the `_typed`
corollaries that they are well typed.
-/

@[expose] public section

noncomputable section

namespace LQT

namespace Mem

open SConstr

-- [PAPER ▶ START] §4.2.3 › Figure 3 "In-place quicksort"

/-- The body of `sort` (Figure 3), with the type variable `n` (`0`) in scope.  Under the `λ`,
`arr` is the variable `0`, and the variable `x` of `memΓ` is `x + 1`. -/
def sortBody : Tm memSig 1 22 :=
 .lam
  (.let_ .omega (.app (.var 10) (.var 0))
   (caseBool .one (.app (.app (.var 17) (.var 0)) lit)
    (.unpack 0 (.app (.var 22) (.var 1))
     (caseUr .one (.var 0)
      (.unpack 2 (.app (.app (.var 14) (.var 3)) (.var 0))
       (caseUr .one (.var 0)
        (casePair .omega (.var 0)
         (.unpack 0 (.app (.var 27) (.var 0))
          (caseUnit .one (.var 0)
           (.unpack 0 (.app (.var 28) (.var 2))
            (caseUnit .one (.var 0)
             (.unpack 0 (.app (.app (.var 21) (.var 2)) (.var 3))
              (caseUr .one (.var 0) (.pack unitE))))))))))))
    (.pack unitE)))

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 20000 in
/-- The body of `sort` is accepted by the inference algorithm at the type of its signature,
with given linear constraint `RW n`. -/
theorem sort_inferred :
    Infers (ctxWk 1 memΓ) ∅ [] [rdA (.tvar 0), wrA (.tvar 0)] sortBody sortS.τ := by
  refine ⟨_, _, Gen.lam' (Gen.let'
    (Gen.app (Gen.var' 10 ![intT, .tvar 0] (by ty_fix) rfl) (Gen.var' 0 ![] (by ty_fix) rfl))
    (Gen.caseBool'
      (Gen.app (Gen.app (Gen.var' 17 ![] (by ty_fix) rfl) (Gen.var' 0 ![] (by ty_fix) rfl)) Gen.lit')
      (Gen.unpack' (Gen.app (Gen.var' 22 ![.tvar 0] (by ty_fix) rfl) (Gen.var' 1 ![] (by ty_fix) rfl))
        (by ty_fix)
       (Gen.caseUr' (Gen.var' 0 ![] (by ty_fix) rfl)
        (Gen.unpack' (Gen.app (Gen.app (Gen.var' 14 ![intT, .tvar 0] (by ty_fix) rfl)
            (Gen.var' 3 ![] (by ty_fix) rfl)) (Gen.var' 0 ![] (by ty_fix) rfl)) (by ty_fix)
          (Gen.caseUr' (Gen.var' 0 ![] (by ty_fix) rfl)
            (Gen.casePair' (Gen.var' 0 ![] (by ty_fix) rfl)
              (Gen.unpack' (Gen.app (Gen.var' 27 ![.tvar 1] (by ty_fix) rfl)
                  (Gen.var' 0 ![] (by ty_fix) rfl)) (by ty_fix)
                (Gen.caseUnit' (Gen.var' 0 ![] (by ty_fix) rfl)
                  (Gen.unpack' (Gen.app (Gen.var' 28 ![.tvar 2] (by ty_fix) rfl)
                      (Gen.var' 2 ![] (by ty_fix) rfl)) (by ty_fix)
                    (Gen.caseUnit' (Gen.var' 0 ![] (by ty_fix) rfl)
                      (Gen.unpack' (Gen.app (Gen.app
                          (Gen.var' 21 ![intT, .tvar 0, .tvar 1, .tvar 2] (by ty_fix) rfl)
                          (Gen.var' 2 ![] (by ty_fix) rfl)) (Gen.var' 3 ![] (by ty_fix) rfl))
                        (by ty_fix)
                        (Gen.caseUr' (Gen.var' 0 ![] (by ty_fix) rfl)
                          (Gen.pack' ![] (by ty_fix) Gen.unit') (by decide))
                        (by decide))
                      (by decide))
                    (by decide))
                  (by decide))
                (by decide))
              (by decide))
            (by decide))
          (by decide))
         (by decide))
        (by decide))
      (Gen.pack' ![] (by ty_fix) Gen.unit') (by decide) (by decide))
    (by decide)) (by decide), ?_⟩
  w_norm
  solve_auto

/-- Hence the body of `sort` is well typed (Figure 6) under `RW n`. -/
theorem sort_typed : ∃ u, Nonempty (HasType memD memSig
    ⟨∅, (([rdA (.tvar 0), wrA (.tvar 0)] : List (Atom Pred 1)) : Multiset (Atom Pred 1))⟩
    (ctxWk 1 memΓ) u sortBody sortS.τ) :=
  sort_inferred.typed'

/-- The body of `partition` (Figure 3), calling the lambda-lifted `go`. -/
def partitionBody : Tm memSig 1 22 :=
 .lam
  (.let_ .omega (.app (.app (.var 18) (.app (.var 10) (.var 0))) lit)
   (.unpack 0 (.app (.app (.var 5) (.var 1)) (.var 0))
    (caseUr .one (.var 0)
     (.app (.app (.app (.app (.app (.var 25) (.var 3)) (.var 2)) (.var 0)) lit)
       (.app (.app (.var 21) (.var 2)) lit)))))

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 20000 in
/-- The body of `partition` is accepted by the inference algorithm at the type of its signature,
with given linear constraint `RW n`. -/
theorem partition_inferred :
    Infers (ctxWk 1 memΓ) ∅ [] [rdA (.tvar 0), wrA (.tvar 0)] partitionBody partitionS.τ := by
  refine ⟨_, _, Gen.lam' (Gen.let'
    (Gen.app (Gen.app (Gen.var' 18 ![] (by ty_fix) rfl)
      (Gen.app (Gen.var' 10 ![intT, .tvar 0] (by ty_fix) rfl) (Gen.var' 0 ![] (by ty_fix) rfl)))
      Gen.lit')
    (Gen.unpack' (Gen.app (Gen.app (Gen.var' 5 ![intT, .tvar 0] (by ty_fix) rfl)
        (Gen.var' 1 ![] (by ty_fix) rfl)) (Gen.var' 0 ![] (by ty_fix) rfl)) (by ty_fix)
      (Gen.caseUr' (Gen.var' 0 ![] (by ty_fix) rfl)
        (Gen.app (Gen.app (Gen.app (Gen.app (Gen.app (Gen.var' 25 ![.tvar 0] (by ty_fix) rfl)
          (Gen.var' 3 ![] (by ty_fix) rfl)) (Gen.var' 2 ![] (by ty_fix) rfl))
          (Gen.var' 0 ![] (by ty_fix) rfl)) Gen.lit')
          (Gen.app (Gen.app (Gen.var' 21 ![] (by ty_fix) rfl) (Gen.var' 2 ![] (by ty_fix) rfl))
            Gen.lit'))
        (by decide))
      (by decide))
    (by decide)) (by decide), ?_⟩
  w_norm
  solve_auto

/-- Hence the body of `partition` is well typed (Figure 6) under `RW n`. -/
theorem partition_typed : ∃ u, Nonempty (HasType memD memSig
    ⟨∅, (([rdA (.tvar 0), wrA (.tvar 0)] : List (Atom Pred 1)) : Multiset (Atom Pred 1))⟩
    (ctxWk 1 memΓ) u partitionBody partitionS.τ) :=
  partition_inferred.typed'

/-- The body of the lambda-lifted `go` (Figure 3): under the five `λ`s, `arr`, `last`, `pivot`,
`l`, `r` are the variables `4`, `3`, `2`, `1`, `0`. -/
def goBody : Tm memSig 1 22 :=
 .lam (.lam (.lam (.lam (.lam
  (caseBool .one (.app (.app (.var 20) (.var 1)) (.var 0))
   (.unpack 0 (.app (.app (.app (.var 23) (.var 4)) (.var 3)) (.var 1))
     (caseUnit .one (.var 0) (.pack (urE (.var 2)))))
   (.unpack 0 (.app (.app (.var 8) (.var 4)) (.var 1))
     (caseUr .one (.var 0)
       (caseBool .one (.app (.app (.var 22) (.var 0)) (.var 4))
          (.unpack 0 (.app (.app (.app (.var 25) (.var 6)) (.var 3)) (.var 2))
             (caseUnit .one (.var 0)
               (.app (.app (.app (.app (.app (.var 29) (.var 7)) (.var 6)) (.var 5)) (.var 4))
                 (.app (.app (.var 25) (.var 3)) lit))))
          (.app (.app (.app (.app (.app (.var 28) (.var 6)) (.var 5)) (.var 4))
            (.app (.app (.var 23) (.var 3)) lit)) (.var 2))))))))))

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 20000 in
/-- The body of `go` is accepted by the inference algorithm at the type of its signature,
with given linear constraint `RW n`. -/
theorem go_inferred :
    Infers (ctxWk 1 memΓ) ∅ [] [rdA (.tvar 0), wrA (.tvar 0)] goBody goS.τ := by
  refine ⟨_, _, Gen.lam' (Gen.lam' (Gen.lam' (Gen.lam' (Gen.lam'
    (Gen.caseBool'
      (Gen.app (Gen.app (Gen.var' 20 ![] (by ty_fix) rfl) (Gen.var' 1 ![] (by ty_fix) rfl))
        (Gen.var' 0 ![] (by ty_fix) rfl))
      (Gen.unpack' (Gen.app (Gen.app (Gen.app (Gen.var' 23 ![.tvar 0] (by ty_fix) rfl)
          (Gen.var' 4 ![] (by ty_fix) rfl)) (Gen.var' 3 ![] (by ty_fix) rfl))
          (Gen.var' 1 ![] (by ty_fix) rfl)) (by ty_fix)
        (Gen.caseUnit' (Gen.var' 0 ![] (by ty_fix) rfl)
          (Gen.pack' ![] (by ty_fix) (Gen.ur' (Gen.var' 2 ![] (by ty_fix) rfl))) (by decide))
        (by decide))
      (Gen.unpack' (Gen.app (Gen.app (Gen.var' 8 ![intT, .tvar 0] (by ty_fix) rfl)
          (Gen.var' 4 ![] (by ty_fix) rfl)) (Gen.var' 1 ![] (by ty_fix) rfl)) (by ty_fix)
        (Gen.caseUr' (Gen.var' 0 ![] (by ty_fix) rfl)
          (Gen.caseBool'
            (Gen.app (Gen.app (Gen.var' 22 ![] (by ty_fix) rfl) (Gen.var' 0 ![] (by ty_fix) rfl))
              (Gen.var' 4 ![] (by ty_fix) rfl))
            (Gen.unpack' (Gen.app (Gen.app (Gen.app (Gen.var' 25 ![.tvar 0] (by ty_fix) rfl)
                (Gen.var' 6 ![] (by ty_fix) rfl)) (Gen.var' 3 ![] (by ty_fix) rfl))
                (Gen.var' 2 ![] (by ty_fix) rfl)) (by ty_fix)
              (Gen.caseUnit' (Gen.var' 0 ![] (by ty_fix) rfl)
                (Gen.app (Gen.app (Gen.app (Gen.app (Gen.app
                  (Gen.var' 29 ![.tvar 0] (by ty_fix) rfl)
                  (Gen.var' 7 ![] (by ty_fix) rfl)) (Gen.var' 6 ![] (by ty_fix) rfl))
                  (Gen.var' 5 ![] (by ty_fix) rfl)) (Gen.var' 4 ![] (by ty_fix) rfl))
                  (Gen.app (Gen.app (Gen.var' 25 ![] (by ty_fix) rfl)
                    (Gen.var' 3 ![] (by ty_fix) rfl)) Gen.lit'))
                (by decide))
              (by decide))
            (Gen.app (Gen.app (Gen.app (Gen.app (Gen.app
              (Gen.var' 28 ![.tvar 0] (by ty_fix) rfl)
              (Gen.var' 6 ![] (by ty_fix) rfl)) (Gen.var' 5 ![] (by ty_fix) rfl))
              (Gen.var' 4 ![] (by ty_fix) rfl))
              (Gen.app (Gen.app (Gen.var' 23 ![] (by ty_fix) rfl)
                (Gen.var' 3 ![] (by ty_fix) rfl)) Gen.lit'))
              (Gen.var' 2 ![] (by ty_fix) rfl))
            (by decide) (by decide))
          (by decide))
        (by decide))
      (by decide) (by decide))
    (by decide)) (by decide)) (by decide)) (by decide)) (by decide), ?_⟩
  w_norm
  solve_auto

/-- Hence the body of `go` is well typed (Figure 6) under `RW n`. -/
theorem go_typed : ∃ u, Nonempty (HasType memD memSig
    ⟨∅, (([rdA (.tvar 0), wrA (.tvar 0)] : List (Atom Pred 1)) : Multiset (Atom Pred 1))⟩
    (ctxWk 1 memΓ) u goBody goS.τ) :=
  go_inferred.typed'

-- [PAPER ◀ END] §4.2.3 › Figure 3

end Mem

end LQT
