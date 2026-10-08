module

public import RequestProject.LQT.Ch4_MemoryOwnership.Kit

/-!
# Swapping two elements of an array (Figure 2)

Paper location: §4.2.2 "Slices", Figure 2 "Swapping two elements of an array".

```
swap :: RW n =⚬ PArray AtomRef n -> Int -> Int -> () ⧀ RW n
swap arr i j
  | i == j = pack ()
  | i > j  = swap arr j i
  | i < j  = let pack (Ur (l, r)) = split arr (i + 1)
                 pack ()          = lendMut l i (λ ai ->
                   let pack () = lendMut r (j - (i + 1)) (λ aj ->
                     let pack (Ur ai_val) = readRef ai
                         pack (Ur aj_val) = readRef aj
                         pack ()          = writeRef aj ai_val
                         pack ()          = writeRef ai aj_val
                     in pack ()) in pack ())
                 pack (Ur _)      = join l r
             in pack ()
```

We write it in the formal language (de Bruijn indices; the APIs are the variables of the
context `memΓ`, see `Setting.lean`), with these differences:

* the guards are nested `case`s on `Bool`, and the last guard `i < j` is `otherwise`;
* `lendMut` is used in the direct style described in `Setting.lean`: `let pack ai' = lendMut l i`
  gives `Ur ai` with `RW p, Lent l p` for a fresh location `p`, and the end of the scope of the
  continuation is the call `unlendMut ai`, which gives back `RW l`;
* the recursive call `swap arr j i` uses the signature of `swap`, which is in the context: the
  definition is checked against its signature, as GHC does for recursive definitions with a
  signature.

The theorem `swap_inferred` says that the body of `swap` is accepted by the inference algorithm
of §6 (constraint generation, Figure 8, then the solver of Figures 9 and 10b) at the type of the
signature, with given constraint `RW n`; `swap_typed` that it is therefore well typed.
-/

@[expose] public section

noncomputable section

namespace LQT

namespace Mem

open SConstr

-- [PAPER ▶ START] §4.2.2 › Figure 2 "Swapping two elements of an array"

/-- The body of `swap` (Figure 2), with the type variable `n` (`0`) in scope.  Under the three
`λ`s, `arr`, `i`, `j` are the variables `2`, `1`, `0`; the variable `x` of `memΓ` is `x + 3`. -/
def swapBody : Tm memSig 1 22 :=
 .lam (.lam (.lam
  (caseBool .one (.app (.app (.var 17) (.var 1)) (.var 0))
   (.pack unitE)
   (caseBool .one (.app (.app (.var 18) (.var 1)) (.var 0))
    (.app (.app (.app (.var 21) (.var 2)) (.var 0)) (.var 1))
    (.unpack 2 (.app (.app (.var 13) (.var 2)) (.app (.app (.var 19) (.var 1)) lit))
     (caseUr .one (.var 0)
      (casePair .omega (.var 0)
       (.unpack 1 (.app (.app (.var 19) (.var 0)) (.var 5))
        (caseUr .one (.var 0)
         (.unpack 1 (.app (.app (.var 21) (.var 3))
             (.app (.app (.var 26) (.var 6)) (.app (.app (.var 25) (.var 7)) lit)))
          (caseUr .one (.var 0)
           (.unpack 0 (.app (.var 17) (.var 2))
            (caseUr .one (.var 0)
             (.unpack 0 (.app (.var 19) (.var 2))
              (caseUr .one (.var 0)
               (.unpack 0 (.app (.app (.var 22) (.var 4)) (.var 2))
                (caseUnit .one (.var 0)
                 (.unpack 0 (.app (.app (.var 23) (.var 7)) (.var 1))
                  (caseUnit .one (.var 0)
                   (.unpack 0 (.app (.var 30) (.var 6))
                    (caseUnit .one (.var 0)
                     (.unpack 0 (.app (.var 31) (.var 9))
                      (caseUnit .one (.var 0)
                       (.unpack 0 (.app (.app (.var 30) (.var 12)) (.var 13))
                        (caseUr .one (.var 0) (.pack unitE))))))))))))))))))))))))))

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 20000 in
/-- The body of `swap` is accepted by the inference algorithm at the type of the signature of
`swap`, `PArray AtomRef n → Int → Int → () ⧀ RW n`, with given linear constraint `RW n`. -/
theorem swap_inferred :
    Infers (ctxWk 1 memΓ) ∅ [] [rdA (.tvar 0), wrA (.tvar 0)] swapBody swapS.τ := by
  refine ⟨_, _, Gen.lam' (Gen.lam' (Gen.lam'
   (Gen.caseBool'
    (Gen.app (Gen.app (Gen.var' 17 ![] (by ty_fix) rfl) (Gen.var' 1 ![] (by ty_fix) rfl))
      (Gen.var' 0 ![] (by ty_fix) rfl))
    (Gen.pack' ![] (by ty_fix) Gen.unit')
    (Gen.caseBool'
     (Gen.app (Gen.app (Gen.var' 18 ![] (by ty_fix) rfl) (Gen.var' 1 ![] (by ty_fix) rfl))
       (Gen.var' 0 ![] (by ty_fix) rfl))
     (Gen.app (Gen.app (Gen.app (Gen.var' 21 ![.tvar 0] (by ty_fix) rfl)
       (Gen.var' 2 ![] (by ty_fix) rfl)) (Gen.var' 0 ![] (by ty_fix) rfl))
       (Gen.var' 1 ![] (by ty_fix) rfl))
     (Gen.unpack' (Gen.app (Gen.app (Gen.var' 13 ![intT, .tvar 0] (by ty_fix) rfl)
        (Gen.var' 2 ![] (by ty_fix) rfl))
        (Gen.app (Gen.app (Gen.var' 19 ![] (by ty_fix) rfl) (Gen.var' 1 ![] (by ty_fix) rfl))
          Gen.lit')) (by ty_fix)
      (Gen.caseUr' (Gen.var' 0 ![] (by ty_fix) rfl)
       (Gen.casePair' (Gen.var' 0 ![] (by ty_fix) rfl)
        (Gen.unpack' (Gen.app (Gen.app (Gen.var' 19 ![intT, .tvar 1] (by ty_fix) rfl)
            (Gen.var' 0 ![] (by ty_fix) rfl)) (Gen.var' 5 ![] (by ty_fix) rfl)) (by ty_fix)
         (Gen.caseUr' (Gen.var' 0 ![] (by ty_fix) rfl)
          (Gen.unpack' (Gen.app (Gen.app (Gen.var' 21 ![intT, .tvar 2] (by ty_fix) rfl)
              (Gen.var' 3 ![] (by ty_fix) rfl))
              (Gen.app (Gen.app (Gen.var' 26 ![] (by ty_fix) rfl) (Gen.var' 6 ![] (by ty_fix) rfl))
                (Gen.app (Gen.app (Gen.var' 25 ![] (by ty_fix) rfl) (Gen.var' 7 ![] (by ty_fix) rfl))
                  Gen.lit'))) (by ty_fix)
           (Gen.caseUr' (Gen.var' 0 ![] (by ty_fix) rfl)
            (Gen.unpack' (Gen.app (Gen.var' 17 ![intT, .tvar 3] (by ty_fix) rfl)
                (Gen.var' 2 ![] (by ty_fix) rfl)) (by ty_fix)
             (Gen.caseUr' (Gen.var' 0 ![] (by ty_fix) rfl)
              (Gen.unpack' (Gen.app (Gen.var' 19 ![intT, .tvar 4] (by ty_fix) rfl)
                  (Gen.var' 2 ![] (by ty_fix) rfl)) (by ty_fix)
               (Gen.caseUr' (Gen.var' 0 ![] (by ty_fix) rfl)
                (Gen.unpack' (Gen.app (Gen.app (Gen.var' 22 ![intT, .tvar 4] (by ty_fix) rfl)
                    (Gen.var' 4 ![] (by ty_fix) rfl)) (Gen.var' 2 ![] (by ty_fix) rfl)) (by ty_fix)
                 (Gen.caseUnit' (Gen.var' 0 ![] (by ty_fix) rfl)
                  (Gen.unpack' (Gen.app (Gen.app (Gen.var' 23 ![intT, .tvar 3] (by ty_fix) rfl)
                      (Gen.var' 7 ![] (by ty_fix) rfl)) (Gen.var' 1 ![] (by ty_fix) rfl)) (by ty_fix)
                   (Gen.caseUnit' (Gen.var' 0 ![] (by ty_fix) rfl)
                    (Gen.unpack' (Gen.app (Gen.var' 30 ![intT, .tvar 2, .tvar 4] (by ty_fix) rfl)
                        (Gen.var' 6 ![] (by ty_fix) rfl)) (by ty_fix)
                     (Gen.caseUnit' (Gen.var' 0 ![] (by ty_fix) rfl)
                      (Gen.unpack' (Gen.app (Gen.var' 31 ![intT, .tvar 1, .tvar 3] (by ty_fix) rfl)
                          (Gen.var' 9 ![] (by ty_fix) rfl)) (by ty_fix)
                       (Gen.caseUnit' (Gen.var' 0 ![] (by ty_fix) rfl)
                        (Gen.unpack' (Gen.app (Gen.app
                            (Gen.var' 30 ![intT, .tvar 0, .tvar 1, .tvar 2] (by ty_fix) rfl)
                            (Gen.var' 12 ![] (by ty_fix) rfl)) (Gen.var' 13 ![] (by ty_fix) rfl))
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
     (by decide) (by decide))
    (by decide) (by decide))
   (by decide)) (by decide)) (by decide), ?_⟩
  w_norm
  solve_auto

/-- Hence the body of `swap` is well typed (Figure 6) under `RW n`. -/
theorem swap_typed : ∃ u, Nonempty (HasType memD memSig
    ⟨∅, (([rdA (.tvar 0), wrA (.tvar 0)] : List (Atom Pred 1)) : Multiset (Atom Pred 1))⟩
    (ctxWk 1 memΓ) u swapBody swapS.τ) :=
  swap_inferred.typed'

-- [PAPER ◀ END] §4.2.2 › Figure 2

end Mem

end LQT
