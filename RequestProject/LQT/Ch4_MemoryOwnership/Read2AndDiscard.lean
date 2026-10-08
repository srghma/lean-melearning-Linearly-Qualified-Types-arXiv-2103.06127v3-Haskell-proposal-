module

public import RequestProject.LQT.Ch4_MemoryOwnership.Kit

/-!
# `read2AndDiscard` (§1)

Paper location: §1 "Introduction", the version of `read2AndDiscard` with linear constraints:

```
read2AndDiscard :: (Read n, Write n) =⚬ UArray a n -> (Ur a, Ur a)
read2AndDiscard arr =
  let pack x  = read arr 0
      pack y  = read arr 1
      ()      = free arr
  in (x, y)
```

The definition is checked against its signature: with the type variables `a` (`0`) and `n`
(`1`) in scope and the given linear constraints `Read n, Write n`, the body has type
`UArray a n →ω (Ur a, Ur a)`.  We prove that it is accepted by the inference algorithm of §6
(constraint generation of Figure 8, then the solver of Figure 9 / 10b), hence well typed.
-/

@[expose] public section

noncomputable section

namespace LQT

namespace Mem

open SConstr

-- [PAPER ▶ START] §1 "Introduction": `read2AndDiscard` with linear constraints

/-- The body of `read2AndDiscard`, in the context `memΓ` (de Bruijn indices: under the `λ`,
`arr` is `0`, `read` is `3 + 1`, `free` is `4 + 1`; under each `let pack` one more variable
is in front). -/
def read2AndDiscard : Tm memSig 2 22 :=
  .lam (.unpack 0 (.app (.app (.var 4) (.var 0)) lit)
    (.unpack 0 (.app (.app (.var 5) (.var 1)) lit)
      (caseUnit .one (.app (.var 7) (.var 2)) (pairE (.var 1) (.var 0)))))

/-- The type of the body: `UArray a n → (Ur a, Ur a)`. -/
def read2AndDiscardTy : Ty Pred 2 :=
  .arr .omega (uarrT (.tvar 0) (.tvar 1)) (pairT (urT (.tvar 0)) (urT (.tvar 0)))

/-- `read2AndDiscard` is accepted by the inference algorithm, with given `Read n, Write n`. -/
theorem read2AndDiscard_inferred :
    Infers (ctxWk 2 memΓ) ∅ [] [rdA (.tvar 1), wrA (.tvar 1)] read2AndDiscard
      read2AndDiscardTy := by
  refine ⟨_, _, Gen.lam' (Gen.unpack' (Gen.app (Gen.app
      (Gen.var' 4 ![.tvar 0, .tvar 1] (by ty_fix) rfl) (Gen.var' 0 ![] (by ty_fix) rfl)) Gen.lit')
      (by ty_fix)
    (Gen.unpack' (Gen.app (Gen.app (Gen.var' 5 ![.tvar 0, .tvar 1] (by ty_fix) rfl)
        (Gen.var' 1 ![] (by ty_fix) rfl)) Gen.lit') (by ty_fix)
      (Gen.caseUnit' (Gen.app (Gen.var' 7 ![.tvar 0, .tvar 1] (by ty_fix) rfl)
          (Gen.var' 2 ![] (by ty_fix) rfl))
        (Gen.pair' (Gen.var' 1 ![] (by ty_fix) rfl) (Gen.var' 0 ![] (by ty_fix) rfl)) (by decide))
      (by decide))
    (by decide)) (by decide), ?_⟩
  w_norm
  solve_auto

/-- Hence `read2AndDiscard` is well typed (Figure 6) under `Read n, Write n`. -/
theorem read2AndDiscard_typed : ∃ u, Nonempty (HasType memD memSig
    ⟨∅, (([rdA (.tvar 1), wrA (.tvar 1)] : List (Atom Pred 2)) : Multiset (Atom Pred 2))⟩
    (ctxWk 2 memΓ) u read2AndDiscard read2AndDiscardTy) :=
  read2AndDiscard_inferred.typed'

-- [PAPER ◀ END] §1 `read2AndDiscard`

end Mem

end LQT
