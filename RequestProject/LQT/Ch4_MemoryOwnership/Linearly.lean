module

public import RequestProject.LQT.Ch4_MemoryOwnership.Kit

/-!
# The `linearly` primitive (§3.2) and the example `f = linearly $ …` (§6.3.2)

Paper location: §3.2 "Restricting to a linear context with `Linearly`" (the primitive
`linearly :: (Linearly =⚬ Ur r) ⊸ Ur r`, and allocating two arrays from one `Linearly`
assumption), and §6.3.2 "An atomic-constraint solver" (the example `f`, which motivates the
choice, by rule Atom_OneL, of the *most recent* occurrence of a linear assumption).

The argument of `linearly` has a qualified type, which the formal language of §5 cannot
express; as explained in `Setting.lean`, we pass it as a linear function from evidence for
`Linearly`, the value type `Evid Linearly = ∃. () ⇐ Linearly`, so that
`linearly :: ∀ r. (Evid Linearly ⊸ Ur r) ⊸ Ur r` is variable `0` of the context `memΓ`.  The
continuation brings `Linearly` into scope by unpacking its argument (`let pack u = ev in
case u of () → …`).  Inside, `Linearly` is a *linear* given constraint that is duplicable
(`memD` has `Linearly` as its only duplicable atom), so it can be used by several calls to
`new`: the solver puts it in its duplicable context `D`, and rule Atom_OneD uses it.

* `twoArraysLinearly_inferred`: the program
  ```
  linearly (λ ev. let pack u = ev in case u of () →
    let pack (Ur a₁) = new 5
        pack (Ur a₂) = new 6
        () = free a₁
        () = free a₂
    in Ur 0)
  ```
  is accepted by the inference algorithm (and therefore well typed, `twoArraysLinearly_typed`),
  as a closed program of type `Ur Int` with no given constraint.
* `fLinearly_inferred`: the example of §6.3.2,
  ```
  f = linearly $ λ ev. let pack u = ev in case u of () →
        let pack (Ur arr) = new 10
            fr :: RW n =⚬ ()
            fr = free arr
            () = fr
        in Ur ()
  ```
  is accepted by the inference algorithm (`fLinearly_typed`: it is well typed).  Inside the
  definition of `fr`, `RW n` is assumed twice, once by the signature of `fr` and once by the
  unpacking of `new 10`.
* `simpleSolve_most_recent`: rule S_ImplOne puts the local linear assumptions of an implication
  at the most recent end of the linear context (`Lout ++ Lloc`), and the atomic solver of
  Figure 10b then consumes a local copy of an atom rather than an outer one: the outer
  assumptions `Lout` are left untouched.  This is the property the paper needs for `f` (the
  call `free arr` in `fr` must use the `RW n` of the signature of `fr`).  Since the copies of
  an atom are equal values, which copy is consumed only matters for the evidence passed at run
  time (§7), not for whether the program is accepted; in the generated constraint of `f`
  (Figure 8 puts the constraint of the body of the `let` before the implication of `fr`), the
  outer `RW n` is moreover consumed by the use of `fr` before the implication is solved.
-/

@[expose] public section

noncomputable section

namespace LQT

-- [PAPER ▶ START] §6.3.2: "Rule Atom-OneL takes care to use the most recent occurrence of q
--   (remember that rule S-ImplOne adds the new hypotheses on the front of the list)"

/-- The atomic solver of Figure 10b consumes the most recent occurrence of a linear atom: if
`q` (not unrestricted) occurs among the local assumptions `Lloc` added by S_ImplOne after the
outer ones `Lout`, the copy consumed is a local one and `Lout` is kept. -/
theorem simpleSolve_most_recent {A : Type*} [DecidableEq A] (l : A) {U : Finset A}
    {Dl Lout Lloc : List A} {q : A} (hU : q ∉ U) (hq : q ∈ Lloc) :
    simpleSolve l U Dl (Lout ++ Lloc) .one q = some (Lout ++ eraseLast q Lloc) := by
  have hq' : q ∈ Lloc.reverse := by simpa using hq
  simp [simpleSolve, hU, hq, eraseLast, List.erase_append_left _ hq']

-- [PAPER ◀ END] §6.3.2, most recent occurrence

namespace Mem

open SConstr

-- [PAPER ▶ START] §3.2 "Restricting to a linear context with Linearly": two arrays allocated
--   from one `Linearly` assumption provided by `linearly`

/-- Two arrays allocated from the `Linearly` assumption provided by `linearly` (§3.2), then
freed.  De Bruijn indices: `linearly` is `0`, `new` is `1`, `free` is `4` in `memΓ`, shifted by
the variables bound in front. -/
def twoArraysLinearly : Tm memSig 0 22 :=
 .app (.var 0)
  (.lam
   (.unpack 0 (.var 0)
    (caseUnit .one (.var 0)
     (.unpack 1 (.app (.var 3) lit)
      (caseUr .one (.var 0)
       (.unpack 1 (.app (.var 5) lit)
        (caseUr .one (.var 0)
         (caseUnit .one (.app (.var 10) (.var 2))
          (caseUnit .one (.app (.var 10) (.var 0))
           (urE lit))))))))))

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 20000 in
/-- The program allocating two arrays inside `linearly` is accepted by the inference algorithm. -/
theorem twoArraysLinearly_inferred : Infers memΓ ∅ [] [] twoArraysLinearly (urT intT) := by
  refine ⟨_, _, Gen.app (Gen.var' 0 ![intT] (by ty_fix) rfl) (Gen.lam'
   (Gen.unpack' (Gen.var' 0 ![] (by ty_fix) rfl) (by ty_fix)
    (Gen.caseUnit' (Gen.var' 0 ![] (by ty_fix) rfl)
     (Gen.unpack' (Gen.app (Gen.var' 3 ![intT] (by ty_fix) rfl) Gen.lit') (by ty_fix)
      (Gen.caseUr' (Gen.var' 0 ![] (by ty_fix) rfl)
       (Gen.unpack' (Gen.app (Gen.var' 5 ![intT] (by ty_fix) rfl) Gen.lit') (by ty_fix)
        (Gen.caseUr' (Gen.var' 0 ![] (by ty_fix) rfl)
         (Gen.caseUnit' (Gen.app (Gen.var' 10 ![intT, .tvar 0] (by ty_fix) rfl)
            (Gen.var' 2 ![] (by ty_fix) rfl))
          (Gen.caseUnit' (Gen.app (Gen.var' 10 ![intT, .tvar 1] (by ty_fix) rfl)
             (Gen.var' 0 ![] (by ty_fix) rfl))
           (Gen.ur' Gen.lit') (by decide))
          (by decide))
         (by decide))
        (by decide))
       (by decide))
      (by decide))
     (by decide))
    (by decide))
   (by decide)), ?_⟩
  w_norm
  solve_auto

/-- Hence `twoArraysLinearly` is well typed (Figure 6), with no given constraint. -/
theorem twoArraysLinearly_typed : ∃ u, Nonempty (HasType memD memSig
    ⟨∅, (([] : List (Atom Pred 0)) : Multiset (Atom Pred 0))⟩ memΓ u twoArraysLinearly (urT intT)) :=
  twoArraysLinearly_inferred.typed'

-- [PAPER ◀ END] §3.2

-- [PAPER ▶ START] §6.3.2, the example `f = linearly $ …`

/-- The example `f` of §6.3.2.  `fr :: RW n =⚬ ()` is a `let` with a signature (and
multiplicity `1`), whose type variable `n` is the one introduced by unpacking `new 10`. -/
def fLinearly : Tm memSig 0 22 :=
 .app (.var 0)
  (.lam
   (.unpack 0 (.var 0)
    (caseUnit .one (.var 0)
     (.unpack 1 (.app (.var 3) lit)
      (caseUr .one (.var 0)
       (.letSig .one ⟨0, rwQ (.tvar 0), unitT⟩ (.app (.var 8) (.var 0))
        (caseUnit .one (.var 0) (urE unitE))))))))

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 20000 in
/-- The example `f` is accepted by the inference algorithm. -/
theorem fLinearly_inferred : Infers memΓ ∅ [] [] fLinearly (urT unitT) := by
  refine ⟨_, _, Gen.app (Gen.var' 0 ![unitT] (by ty_fix) rfl) (Gen.lam'
   (Gen.unpack' (Gen.var' 0 ![] (by ty_fix) rfl) (by ty_fix)
    (Gen.caseUnit' (Gen.var' 0 ![] (by ty_fix) rfl)
     (Gen.unpack' (Gen.app (Gen.var' 3 ![intT] (by ty_fix) rfl) Gen.lit') (by ty_fix)
      (Gen.caseUr' (Gen.var' 0 ![] (by ty_fix) rfl)
       (Gen.letSig' (Gen.app (Gen.var' 8 ![intT, .tvar 0] (by ty_fix) rfl)
           (Gen.var' 0 ![] (by ty_fix) rfl))
        (Gen.caseUnit' (Gen.var' 0 ![] (by ty_fix) rfl) (Gen.ur' Gen.unit') (by decide))
        (by decide))
       (by decide))
      (by decide))
     (by decide))
    (by decide))
   (by decide)), ?_⟩
  w_norm
  solve_auto

/-- Hence `fLinearly` is well typed (Figure 6), with no given constraint. -/
theorem fLinearly_typed : ∃ u, Nonempty (HasType memD memSig
    ⟨∅, (([] : List (Atom Pred 0)) : Multiset (Atom Pred 0))⟩ memΓ u fLinearly (urT unitT)) :=
  fLinearly_inferred.typed'

-- [PAPER ◀ END] §6.3.2, the example `f`

-- [NOT IN PAPER ▶ START] §4.1 "Capability constraints": the API of atomic references at work
--   (the paper gives the API but no program using it)

/-- A program using the atomic-reference API of §4.1:
```
linearly (λ ev. let pack u = ev in case u of () →
  let pack (Ur r)  = newRef
      pack ()      = writeRef r 0
      pack (Ur v)  = readRef r
      ()           = freeRef r
  in Ur v)
```
(`newRef`, `readRef`, `writeRef`, `freeRef` are `5`, `6`, `7`, `8` in `memΓ`). -/
def refExample : Tm memSig 0 22 :=
 .app (.var 0)
  (.lam
   (.unpack 0 (.var 0)
    (caseUnit .one (.var 0)
     (.unpack 1 (.var 7)
      (caseUr .one (.var 0)
       (.unpack 0 (.app (.app (.var 11) (.var 0)) lit)
        (caseUnit .one (.var 0)
         (.unpack 0 (.app (.var 11) (.var 1))
          (caseUr .one (.var 0)
           (caseUnit .one (.app (.var 15) (.var 3)) (urE (.var 0))))))))))))

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 20000 in
/-- The reference program is accepted by the inference algorithm. -/
theorem refExample_inferred : Infers memΓ ∅ [] [] refExample (urT intT) := by
  refine ⟨_, _, Gen.app (Gen.var' 0 ![intT] (by ty_fix) rfl) (Gen.lam'
   (Gen.unpack' (Gen.var' 0 ![] (by ty_fix) rfl) (by ty_fix)
    (Gen.caseUnit' (Gen.var' 0 ![] (by ty_fix) rfl)
     (Gen.unpack' (Gen.var' 7 ![intT] (by ty_fix) rfl) (by ty_fix)
      (Gen.caseUr' (Gen.var' 0 ![] (by ty_fix) rfl)
       (Gen.unpack' (Gen.app (Gen.app (Gen.var' 11 ![intT, .tvar 0] (by ty_fix) rfl)
           (Gen.var' 0 ![] (by ty_fix) rfl)) Gen.lit') (by ty_fix)
        (Gen.caseUnit' (Gen.var' 0 ![] (by ty_fix) rfl)
         (Gen.unpack' (Gen.app (Gen.var' 11 ![intT, .tvar 0] (by ty_fix) rfl)
             (Gen.var' 1 ![] (by ty_fix) rfl)) (by ty_fix)
          (Gen.caseUr' (Gen.var' 0 ![] (by ty_fix) rfl)
           (Gen.caseUnit' (Gen.app (Gen.var' 15 ![intT, .tvar 0] (by ty_fix) rfl)
              (Gen.var' 3 ![] (by ty_fix) rfl))
            (Gen.ur' (Gen.var' 0 ![] (by ty_fix) rfl)) (by decide))
           (by decide))
          (by decide))
         (by decide))
        (by decide))
       (by decide))
      (by decide))
     (by decide))
    (by decide))
   (by decide)), ?_⟩
  w_norm
  solve_auto

/-- Hence `refExample` is well typed (Figure 6), with no given constraint. -/
theorem refExample_typed : ∃ u, Nonempty (HasType memD memSig
    ⟨∅, (([] : List (Atom Pred 0)) : Multiset (Atom Pred 0))⟩ memΓ u refExample (urT intT)) :=
  refExample_inferred.typed'

-- [NOT IN PAPER ◀ END] §4.1, atomic references

end Mem

end LQT
